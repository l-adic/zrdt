#!/usr/bin/env python3
"""A small frame client for zrdtd (layouts: core/Zrdt/Proto.lean).

    zrdtd_client.py vectors ZRDTD [VECTORS_JSON]   rung 6: every session step gives its reply
    zrdtd_client.py smoke ZRDTD [N]                NEW, N chained ACCEPTs, HEADS, ENCODE, CLOSE,
                                                   OPEN of that blob; prints round-trip times
    zrdtd_client.py framing ZRDTD                  short writes, pipelining, end of input

ZRDTD is the path of the zrdtd binary. It is started with LEAN_ABORT_ON_PANIC=1.
Python 3.8 or later, standard library only. Exit code 0 when every check passes.
"""

import hashlib
import json
import os
import struct
import subprocess
import sys
import time

OP = {name: i + 1 for i, name in enumerate(
    "VERSION NEW OPEN SALVAGE COMMIT HASH ACCEPT HEADS HAS GET REACH_SET MERGE CLASSIFY "
    "ENCODE CLOSE".split())}
OK, MISSING, COLLISION, WRONG_CHAT, TOO_LARGE, MALFORMED, UNVERIFIABLE, NOT_FOUND = range(8)


def u32(n):
    return struct.pack(">I", n)


def bstr(b):
    return u32(len(b)) + b


def chat(s):
    return bstr(s.encode())


def digests(ds):
    return u32(len(ds)) + b"".join(ds)


def parts(group, commit, links, author):
    return group + commit + digests(links) + author


def read_digests(b, off):
    n = struct.unpack_from(">I", b, off)[0]
    off += 4
    return [b[off + 32 * i: off + 32 * (i + 1)] for i in range(n)], off + 32 * n


def record_encoding(group, commit, links, author):
    """The record encoding of docs/PLAN.md §3.4, written here independently of the Lean code."""
    links = sorted(set(links))
    return b"zrdt2" + group + commit + u32(len(links)) + b"".join(links) + author


class Zrdtd:
    def __init__(self, path, stderr=None):
        env = dict(os.environ, LEAN_ABORT_ON_PANIC="1")
        self.p = subprocess.Popen([path], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=stderr, env=env, bufsize=0)

    def send(self, payload):
        self.p.stdin.write(u32(len(payload)) + payload)

    def recv(self):
        n = struct.unpack(">I", self.read_exact(4))[0]
        return self.read_exact(n)

    def read_exact(self, n):
        out = bytearray()
        while len(out) < n:
            chunk = self.p.stdout.read(n - len(out))
            if not chunk:
                raise EOFError("zrdtd closed its output after %d of %d bytes" % (len(out), n))
            out += chunk
        return bytes(out)

    def call(self, op, body=b""):
        self.send(bytes([OP[op]]) + body)
        return self.recv()

    def close(self):
        self.p.stdin.close()
        return self.p.wait(timeout=30)


def run_vectors(path, vectors_path):
    with open(vectors_path) as f:
        vectors = json.load(f)
    failures = 0
    total = 0
    for session in vectors["sessions"]:
        z = Zrdtd(path, stderr=subprocess.DEVNULL)
        for step in session["steps"]:
            total += 1
            z.send(bytes.fromhex(step["request"]))
            got = z.recv().hex()
            if got != step["reply"]:
                failures += 1
                print("MISMATCH %s / %s:\n  want %s\n  got  %s" % (
                    session["name"], step["name"], step["reply"][:200], got[:200]))
        code = z.close()
        if code != 0:
            failures += 1
            print("session %s: zrdtd exited with %d" % (session["name"], code))
    print("vectors: %d steps in %d sessions, %d mismatches (build %s)" % (
        total, len(vectors["sessions"]), failures, vectors["build"]))
    return failures == 0


def smoke(path, n):
    z = Zrdtd(path)
    group, author = b"\x67" * 32, b"\xa1" * 16
    ok = True

    for _ in range(200):  # warm up
        assert z.call("VERSION")[0] == OK
    t0 = time.perf_counter()
    for _ in range(1000):
        assert z.call("VERSION")[0] == OK
    version_us = (time.perf_counter() - t0) / 1000 * 1e6

    assert z.call("NEW", chat("bench") + group) == bytes([OK])
    prev = None
    spent = 0.0
    first_tenth = 0.0
    for i in range(n):
        commit = hashlib.sha256(b"message %d" % i).digest()
        links = [prev] if prev else []
        body = chat("bench") + parts(group, commit, links, author)
        t0 = time.perf_counter()
        reply = z.call("ACCEPT", body)
        spent += time.perf_counter() - t0
        if i == n // 10 - 1:
            first_tenth = spent
        if reply[0] != OK:
            print("ACCEPT %d: status %d" % (i, reply[0]))
            return False
        # Check the digest against an independent encoding and Python's hashlib.
        if reply[1:] != hashlib.sha256(record_encoding(group, commit, links, author)).digest():
            print("ACCEPT %d: digest differs from hashlib" % i)
            ok = False
        prev = reply[1:]
    accept_us = spent / n * 1e6
    tenth = max(n // 10, 1)
    first_us = first_tenth / tenth * 1e6

    heads = z.call("HEADS", chat("bench"))
    ok &= heads == bytes([OK]) + digests([prev])
    t0 = time.perf_counter()
    blob_reply = z.call("ENCODE", chat("bench"))
    encode_ms = (time.perf_counter() - t0) * 1e3
    assert blob_reply[0] == OK
    blob = blob_reply[5:]
    ok &= z.call("CLOSE", chat("bench")) == bytes([OK])
    ok &= z.call("HEADS", chat("bench"))[0] == 0x82  # NO_CHAT
    t0 = time.perf_counter()
    opened = z.call("OPEN", chat("bench") + group + b"\x00" + bstr(blob))
    open_ms = (time.perf_counter() - t0) * 1e3
    ok &= opened == bytes([OK])
    ok &= z.call("HEADS", chat("bench")) == heads
    ok &= z.call("ENCODE", chat("bench")) == blob_reply
    reach = z.call("REACH_SET", chat("bench") + digests([prev]))
    ok &= reach[0] == OK and len(read_digests(reach, 1)[0]) == n
    code = z.close()
    ok &= code == 0
    print("smoke: %s" % ("pass" if ok else "FAIL"))
    print("  VERSION round trip: %.1f us (mean of 1000)" % version_us)
    print("  ACCEPT round trip, %d chained records: %.1f us each (first tenth: %.1f us each)" % (
        n, accept_us, first_us))
    print("  ENCODE of %d records (%d bytes): %.1f ms; OPEN of that blob: %.1f ms" % (
        n, len(blob), encode_ms, open_ms))
    return ok


def framing(path):
    ok = True
    # Short writes: the frame arrives a byte at a time, with pauses.
    z = Zrdtd(path, stderr=subprocess.DEVNULL)
    frame = u32(1) + bytes([OP["VERSION"]])
    for b in frame:
        z.p.stdin.write(bytes([b]))
        time.sleep(0.02)
    ok &= z.recv()[0] == OK
    body = bytes([OP["NEW"]]) + chat("c") + b"\x67" * 32
    whole = u32(len(body)) + body
    z.p.stdin.write(whole[:3])
    time.sleep(0.05)
    z.p.stdin.write(whole[3:10])
    time.sleep(0.05)
    z.p.stdin.write(whole[10:])
    ok &= z.recv() == bytes([OK])
    # Pipelining: 200 requests in one write; the replies come back in order.
    reqs = []
    for i in range(200):
        d = bytes([i % 256]) * 32
        p = bytes([OP["HAS"]]) + chat("c") + d
        reqs.append(u32(len(p)) + p)
    p = bytes([OP["HEADS"]]) + chat("c")
    reqs.append(u32(len(p)) + p)
    z.p.stdin.write(b"".join(reqs))
    replies = [z.recv() for _ in reqs]
    ok &= all(r == bytes([OK, 0]) for r in replies[:200]) and replies[200] == bytes([OK]) + u32(0)
    ok &= z.close() == 0
    print("framing: short writes and 201 pipelined requests: %s" % ("pass" if ok else "FAIL"))
    # End of input inside a frame: exit code 1 and a line on stderr.
    for cut, what in [(b"\x00\x00", "inside a header"), (u32(10) + b"\x01\x02", "inside a body")]:
        q = subprocess.run([path], input=cut, capture_output=True, timeout=30,
                           env=dict(os.environ, LEAN_ABORT_ON_PANIC="1"))
        good = q.returncode == 1 and b"ended inside" in q.stderr and q.stdout == b""
        ok &= good
        print("framing: end of input %s: exit %d, %s" % (
            what, q.returncode, "pass" if good else "FAIL " + repr(q.stderr)))
    # End of input between frames: exit 0, no output.
    q = subprocess.run([path], input=b"", capture_output=True, timeout=30,
                       env=dict(os.environ, LEAN_ABORT_ON_PANIC="1"))
    good = q.returncode == 0 and q.stdout == b""
    ok &= good
    print("framing: end of input between frames: exit %d, %s" % (
        q.returncode, "pass" if good else "FAIL"))
    return ok


def main(argv):
    if len(argv) < 3 or argv[1] not in ("vectors", "smoke", "framing"):
        print(__doc__)
        return 2
    path = argv[2]
    if argv[1] == "vectors":
        here = os.path.dirname(os.path.abspath(__file__))
        ok = run_vectors(path, argv[3] if len(argv) > 3 else os.path.join(here, "vectors.json"))
    elif argv[1] == "smoke":
        ok = smoke(path, int(argv[3]) if len(argv) > 3 else 1000)
    else:
        ok = framing(path)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
