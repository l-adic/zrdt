#!/usr/bin/env python3
"""A fake zrdt desktop: the git endpoint of ENDPOINT.md, in memory, for tests.

One process plays every member's desktop: the bearer token says which member is asking. It models
what the helper can observe of BUILD_M1 §4 (the git app on piece stores):

- a group's members, each with an identity-key tag; a push record's audience is the group's
  members (with their tags) when it is published;
- a member holds a record's content (its opening) iff the record's audience seats him; other
  records are structure only (counted as notGiven), as in JOIN's relative stores;
- the checks of GIT_PREPARE (BUILD_M1 §4.3) over the pusher's own table: BAD_OBJECTS, BAD_REF,
  NEEDS_CREATE, ROOT, OLD_OBJECT, GATE (with the name rule), and for shares BAD_SHARE,
  KEY_CHANGED, COVERS_CHANGED;
- the register (BUILD_M1 §4.4): an assignment (d, n := v) is superseded when a held record e
  assigns n with v in its ``old`` list and d is reachable from e's links;
- objects are served only from records the asking member holds.

It is not a security boundary and has no Signal, CDN or zrdtd in it. Usage:

  fake_endpoint.py --config cfg.json (--listen 127.0.0.1:0 | --unix PATH) [--port-file F]

cfg.json: {"adminToken": "...", "pieceSize": 1048576,
           "accounts": {"alice": "<token>", ...}, "groups": {"Code": ["alice", "bob"]}}
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import secrets
import socketserver
import sys
import threading
import time
import urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
from zrdt_git.objects import (ObjectError, check_stream, group_name_problem, is_oid,  # noqa: E402
                              parse_commit, parse_tree, ref_name_problem, repo_name_problem,
                              split_raw)

PROTOCOL = 1
MAX_UPDATES = 64
MAX_OBJECTS = 200000


class HttpError(Exception):
    def __init__(self, code: int, error: str, message: str):
        super().__init__(message)
        self.code = code
        self.error = error
        self.message = message


class Refuse(Exception):
    def __init__(self, reason: str, message: str, **extra):
        super().__init__(message)
        self.body = dict(status="refused", reason=reason, message=message, **extra)


class Record:
    def __init__(self, **kw):
        self.__dict__.update(kw)

    def seats(self, member: str, tag: int | None = None) -> bool:
        return any(m == member and (tag is None or t == tag) for m, t in self.audience)


class Channel:
    def __init__(self, group: str, repo: str):
        self.group = group
        self.repo = repo
        self.records: list[Record] = []
        self.by_digest: dict[str, Record] = {}
        self.heads: set[str] = set()
        self.objects: dict[str, bytes] = {}
        self.uploads: dict[str, dict] = {}

    def ancestors(self, digest: str, memo: dict) -> set[str]:
        """Records strictly reachable from ``digest`` through links."""
        if digest in memo:
            return memo[digest]
        seen: set[str] = set()
        stack = list(self.by_digest[digest].links)
        while stack:
            d = stack.pop()
            if d in seen:
                continue
            seen.add(d)
            stack.extend(self.by_digest[d].links)
        memo[digest] = seen
        return seen


class World:
    def __init__(self, cfg: dict):
        self.lock = threading.RLock()
        self.admin_token = cfg.get("adminToken") or secrets.token_hex(16)
        self.piece_size = int(cfg.get("pieceSize", 1 << 20))
        self.max_stream = int(cfg.get("maxStream", 64 << 20))
        self.max_objects_per_request = int(cfg.get("maxObjectsPerRequest", 256))
        self.tokens: dict[str, str] = {}
        self.tags: dict[str, int] = {}
        self.groups: dict[str, set[str]] = {}
        self.channels: dict[tuple[str, str], Channel] = {}
        for name, token in cfg.get("accounts", {}).items():
            self.add_account(name, token)
        for g, members in cfg.get("groups", {}).items():
            self.groups[g] = set(members)

    def add_account(self, name: str, token: str) -> None:
        self.tokens[token] = name
        self.tags.setdefault(name, 1)

    # -- helpers ----------------------------------------------------------------------------

    def member_of(self, token: str | None) -> str:
        m = self.tokens.get(token or "")
        if m is None:
            raise HttpError(401, "unauthorized", "unknown token")
        return m

    def channel(self, member: str, group: str, repo: str) -> Channel:
        if group_name_problem(group) or repo_name_problem(repo):
            raise HttpError(400, "bad_request", "bad group alias or repository name")
        if member not in self.groups.get(group, set()):
            # Same answer for "no such group" and "not a member": no existence oracle.
            raise HttpError(404, "no_group", "no group %r on this desktop" % group)
        key = (group, repo)
        if key not in self.channels:
            self.channels[key] = Channel(group, repo)
        return self.channels[key]

    def audience(self, group: str) -> list[tuple[str, int]]:
        return sorted((m, self.tags[m]) for m in self.groups[group])

    @staticmethod
    def held(ch: Channel, member: str) -> list[Record]:
        return [r for r in ch.records if r.seats(member)]

    @staticmethod
    def compare_code(heads) -> str:
        h = hashlib.sha256(("zrdt-heads:" + ",".join(sorted(heads))).encode()).hexdigest()
        return "-".join(h[i:i + 5] for i in range(0, 30, 5))

    def live(self, ch: Channel, held: list[Record]) -> dict[str, list[tuple[Record, dict]]]:
        memo: dict = {}
        assigns = [(r, u) for r in held for u in r.updates]
        out: dict[str, list[tuple[Record, dict]]] = {}
        for d, u in assigns:
            superseded = False
            for e, w in assigns:
                if w["name"] != u["name"] or e is d:
                    continue
                if d.digest not in ch.ancestors(e.digest, memo):
                    continue
                # A value is replaced by an assignment that names it in `old`; a delete is
                # replaced by any later assignment of the name that saw it.
                if u["new"] is None or u["new"] in w["old"]:
                    superseded = True
                    break
            if not superseded:
                out.setdefault(u["name"], []).append((d, u))
        return out

    # -- API --------------------------------------------------------------------------------

    def hello(self, member: str) -> dict:
        return {"protocol": PROTOCOL, "app": "git-sha256", "objectFormat": "sha256", "member": member,
                "pieceSize": self.piece_size, "maxStream": self.max_stream,
                "maxObjectsPerRequest": self.max_objects_per_request}

    def state(self, member: str, ch: Channel) -> dict:
        held = self.held(ch, member)
        refs = []
        for name, vals in sorted(self.live(ch, held).items()):
            values = [{"value": u["new"], "record": d.digest, "forced": u["forced"], "author": d.author}
                      for d, u in vals if u["new"] is not None]
            if values:
                refs.append({"name": name, "values": sorted(values, key=lambda v: (v["value"], v["record"]))})
        return {
            "group": ch.group, "repo": ch.repo,
            "members": [{"member": m, "self": m == member} for m in sorted(self.groups[ch.group])],
            "heads": sorted(ch.heads),
            "compareCode": self.compare_code(ch.heads),
            "records": [self.record_json(r, member) for r in held],
            "notGiven": len(ch.records) - len(held),
            "pending": [],
            "refs": refs,
        }

    @staticmethod
    def record_json(r: Record, member: str) -> dict:
        return {"record": r.digest, "seq": r.seq, "author": r.author,
                "provenance": "self" if r.author == member else "live",
                "share": r.share, "links": list(r.links), "objects": list(r.objects),
                "covers": list(r.covers), "updates": [dict(u) for u in r.updates]}

    def create_upload(self, member: str, ch: Channel, body: dict) -> dict:
        size = body.get("size")
        if not isinstance(size, int) or not (1 <= size <= self.max_stream):
            raise HttpError(413 if isinstance(size, int) and size > 0 else 400, "too_large",
                            "an object stream is 1..%d bytes" % self.max_stream)
        now = time.time()
        for k in [k for k, u in ch.uploads.items() if now - u["created"] > 3600]:
            del ch.uploads[k]
        uid = secrets.token_hex(12)
        n = (size + self.piece_size - 1) // self.piece_size
        ch.uploads[uid] = {"owner": member, "size": size, "pieceSize": self.piece_size, "pieces": {},
                           "count": n, "created": now}
        return {"upload": uid, "pieceSize": self.piece_size, "pieces": n}

    def put_piece(self, member: str, ch: Channel, uid: str, index: int, body: dict) -> dict:
        up = ch.uploads.get(uid)
        if up is None or up["owner"] != member:
            raise HttpError(404, "no_upload", "no such upload")
        if not (0 <= index < up["count"]):
            raise HttpError(400, "bad_request", "piece index out of range")
        try:
            data = base64.b64decode(str(body.get("data", "")).encode("ascii"), validate=True)
        except (ValueError, UnicodeEncodeError):
            raise HttpError(400, "bad_request", "piece data is not base64")
        want = up["pieceSize"] if index < up["count"] - 1 else up["size"] - up["pieceSize"] * (up["count"] - 1)
        if len(data) != want:
            raise HttpError(400, "bad_piece", "piece %d has %d bytes, expected %d" % (index, len(data), want))
        if hashlib.sha256(data).hexdigest() != body.get("sha256"):
            raise HttpError(400, "bad_piece", "piece %d does not match its sha256" % index)
        up["pieces"][index] = data
        return {"ok": True}

    def objects(self, member: str, ch: Channel, body: dict) -> dict:
        ids = body.get("ids")
        if not isinstance(ids, list) or len(ids) > self.max_objects_per_request or not all(is_oid(i) for i in ids):
            raise HttpError(400, "bad_request", "ids: at most %d object ids" % self.max_objects_per_request)
        allowed: set[str] = set()
        for r in self.held(ch, member):
            allowed.update(r.objects)
        out, missing = [], []
        for oid in ids:
            if oid in allowed and oid in ch.objects:
                out.append({"id": oid, "raw": base64.b64encode(ch.objects[oid]).decode("ascii")})
            else:
                missing.append(oid)
        return {"objects": out, "missing": missing}

    # -- the push checks (BUILD_M1 §4.3, over the pusher's table) ---------------------------

    def push(self, author: str, ch: Channel, req: dict) -> dict:
        share = bool(req.get("share", False))
        dry = bool(req.get("dryRun", False))
        create = bool(req.get("create", False))
        updates = self.parse_updates(req.get("updates"))
        ids = req.get("objects", [])
        if not isinstance(ids, list) or not all(is_oid(i) for i in ids) or len(ids) > MAX_OBJECTS:
            raise HttpError(400, "bad_request", "objects must be a list of object ids")
        if ids != sorted(set(ids)):
            raise Refuse("BAD_OBJECTS", "object ids must be strictly increasing")
        # 1. objects: the stream, reassembled from the pieces, must be exactly the listed objects
        objs: dict[str, tuple[str, bytes]] = {}
        uid = req.get("upload")
        if ids:
            up = ch.uploads.get(uid) if isinstance(uid, str) else None
            if up is None or up["owner"] != author:
                raise Refuse("BAD_OBJECTS", "the push lists objects but names no upload of yours")
            if len(up["pieces"]) != up["count"]:
                raise Refuse("BAD_OBJECTS", "the upload is missing %d piece(s)" % (up["count"] - len(up["pieces"])))
            stream = b"".join(up["pieces"][i] for i in range(up["count"]))
            try:
                walked = check_stream(stream)
            except ObjectError as e:
                raise Refuse("BAD_OBJECTS", str(e), objects=[e.oid] if e.oid else [])
            if [w[0] for w in walked] != ids:
                raise Refuse("BAD_OBJECTS", "the uploaded objects are not the listed objects")
            for oid, kind, off, ln in walked:
                objs[oid] = (kind, stream[off:off + ln])
        elif uid is not None:
            raise Refuse("BAD_OBJECTS", "an upload was named but no objects were listed")
        for u in updates:
            p = ref_name_problem(u["name"])
            if p:
                raise Refuse("BAD_REF", "%s: %s" % (u["name"], p), name=u["name"])
        if not updates:
            raise Refuse("BAD_REF", "a push updates at least one ref")
        if len(updates) > MAX_UPDATES:
            raise Refuse("BAD_REF", "at most %d ref updates per push" % MAX_UPDATES)

        table = self.held(ch, author)
        audience = self.audience(ch.group)
        checked = [(m, t) for m, t in audience if m != author and t != 0]
        table_objs: set[str] = set()
        for r in table:
            table_objs.update(r.objects)

        def entitled(m: str, t: int, o: str) -> bool:
            return any(o in r.objects and r.seats(m, t) for r in table)

        def key_changed(m: str, t: int) -> bool:
            return any(mm == m and tt != t and tt != 0 for r in table for mm, tt in r.audience)

        def assigned(m: str, t: int, name: str, v: str) -> bool:
            return any(r.seats(m, t) and any(w["name"] == name and w["new"] == v for w in r.updates)
                       for r in table)

        commits: dict[str, tuple[str, list[str]]] = {}
        refs_out: set[str] = set()
        for oid, (kind, raw) in objs.items():
            _, content = split_raw(raw)
            if kind == "commit":
                tree, parents = parse_commit(content)
                commits[oid] = (tree, parents)
                refs_out.add(tree)
                refs_out.update(parents)
            elif kind == "tree":
                refs_out.update(e[1] for e in parse_tree(content))
        for u in updates:
            refs_out.update(u["old"])
            if u["new"] is not None:
                refs_out.add(u["new"])
        refs_out -= set(objs)

        if not ch.records and not create:
            raise Refuse("NEEDS_CREATE", "%s/%s holds no push; push with create to start it" % (ch.group, ch.repo))
        if not share:
            # 2. root rule (G-F1)
            if ch.records:
                roots = sorted(c for c, (_, ps) in commits.items() if not ps)
                if roots:
                    raise Refuse("ROOT", "a root commit cannot enter a repository with history", objects=roots)
            # 3. freshness (G-M6)
            old = sorted(set(objs) & table_objs)
            if old:
                raise Refuse("OLD_OBJECT", "%d object(s) were already carried by earlier pushes" % len(old),
                             objects=old)
            # 4. the gate, with the name rule
            seats = []
            for m, t in checked:
                missing = sorted(o for o in refs_out if not entitled(m, t, o))
                names = sorted({u["name"] for u in updates for v in u["old"] if not assigned(m, t, u["name"], v)})
                if missing or names:
                    seats.append({"member": m, "reason": "KEY_CHANGED" if key_changed(m, t) else "NEW",
                                  "missing": len(missing), "names": names})
            if seats:
                raise Refuse("GATE", "%s ha%s not been given the history this push builds on"
                             % (", ".join(s["member"] for s in seats), "s" if len(seats) == 1 else "ve"),
                             seats=seats)
            covers: list[str] = []
        else:
            # 5. a share: exactly the updates' commits with their whole trees, no deletes
            news = {u["new"] for u in updates}
            if None in news:
                raise Refuse("BAD_SHARE", "a share cannot delete a ref")
            if any(v != u["new"] for u in updates for v in u["old"]):
                raise Refuse("BAD_SHARE", "a share re-asserts current values only (old must equal new)")
            if set(commits) != news:
                raise Refuse("BAD_SHARE", "a share carries exactly the commits its updates name")
            for c, (tree, _) in commits.items():
                stack = [tree]
                while stack:
                    o = stack.pop()
                    if o not in objs:
                        raise Refuse("BAD_SHARE", "a share carries the whole tree of its commits", objects=[o])
                    kind, raw = objs[o]
                    if kind == "tree":
                        stack.extend(e[1] for e in parse_tree(split_raw(raw)[1]))
            covers = sorted(m for m, t in checked
                            if any(o in table_objs and not entitled(m, t, o) for o in objs))
            changed = [m for m, t in checked if m in covers and key_changed(m, t)]
            if changed:
                raise Refuse("KEY_CHANGED", "a share would cover %s, whose key changed" % ", ".join(changed),
                             seats=[{"member": m, "reason": "KEY_CHANGED"} for m in changed])
            expect = req.get("covers")
            if expect is None or sorted(expect) != covers:
                raise Refuse("COVERS_CHANGED", "this share covers: %s" % (", ".join(covers) or "nobody"),
                             covers=covers)
        if dry:
            return {"status": "ok", "record": None, "audience": [m for m, _ in audience], "covers": covers}
        links = sorted(ch.heads)
        body = {"group": ch.group, "repo": ch.repo, "author": author, "audience": audience, "share": share,
                "updates": updates, "objects": ids, "covers": covers, "links": links,
                "nonce": secrets.token_hex(32)}
        digest = hashlib.sha256(json.dumps(body, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        rec = Record(digest=digest, seq=len(ch.records) + 1, author=author, audience=audience, share=share,
                     updates=updates, objects=ids, covers=covers, links=links)
        ch.records.append(rec)
        ch.by_digest[digest] = rec
        ch.heads = {digest}
        for oid, (_, raw) in objs.items():
            ch.objects.setdefault(oid, raw)
        if isinstance(uid, str):
            ch.uploads.pop(uid, None)
        return {"status": "ok", "record": digest, "audience": [m for m, _ in audience], "covers": covers}

    @staticmethod
    def parse_updates(raw) -> list[dict]:
        if not isinstance(raw, list):
            raise HttpError(400, "bad_request", "updates must be a list")
        out = []
        names = set()
        for u in raw:
            if not isinstance(u, dict):
                raise HttpError(400, "bad_request", "an update is an object")
            name, old, new, forced = u.get("name"), u.get("old", []), u.get("new"), u.get("forced", False)
            if not isinstance(name, str) or name in names:
                raise HttpError(400, "bad_request", "update names must be distinct strings")
            if not isinstance(old, list) or not all(is_oid(v) for v in old) or old != sorted(set(old)):
                raise HttpError(400, "bad_request", "old must be a sorted list of object ids")
            if new is not None and not is_oid(new):
                raise HttpError(400, "bad_request", "new must be an object id or null")
            if not isinstance(forced, bool):
                raise HttpError(400, "bad_request", "forced must be a boolean")
            names.add(name)
            out.append({"name": name, "old": old, "new": new, "forced": forced})
        return sorted(out, key=lambda u: u["name"])

    # -- admin (test only) ------------------------------------------------------------------

    def admin(self, method: str, parts: list[str], body: dict) -> dict:
        op = parts[1] if len(parts) > 1 else ""
        if method == "POST" and op == "members":
            g, m = body["group"], body["member"]
            if body.get("token"):
                self.add_account(m, body["token"])
            if m not in self.tags:
                raise HttpError(400, "bad_request", "unknown account and no token")
            self.groups.setdefault(g, set()).add(m)
            return {"ok": True, "members": sorted(self.groups[g])}
        if method == "POST" and op == "remove":
            self.groups.get(body["group"], set()).discard(body["member"])
            return {"ok": True}
        if method == "POST" and op == "key":
            self.tags[body["member"]] += 1
            return {"ok": True, "tag": self.tags[body["member"]]}
        if method == "POST" and op == "tamper":
            ch = self.channels[(body["group"], body["repo"])]
            raw = bytearray(ch.objects[body["id"]])
            raw[-1] ^= 0x01
            ch.objects[body["id"]] = bytes(raw)
            return {"ok": True}
        if method == "GET" and op == "dump":
            return {"channels": [{"group": c.group, "repo": c.repo, "records": [
                {"record": r.digest, "seq": r.seq, "author": r.author, "share": r.share,
                 "audience": r.audience, "updates": r.updates, "objects": len(r.objects), "covers": r.covers}
                for r in c.records]} for c in self.channels.values()]}
        raise HttpError(404, "not_found", "no such admin call")


ROUTE = re.compile(r"^/v1/git/([^/]+)/([^/]+)(?:/(uploads|pushes|objects)(?:/([^/]+)/pieces/(\d+))?)?$")


def make_handler(world: World, log):
    class Handler(BaseHTTPRequestHandler):
        server_version = "zrdt-fake-endpoint/1"

        def log_message(self, fmt, *args):  # noqa: N802
            if log:
                log.write("%s\n" % (fmt % args))
                log.flush()

        def _reply(self, code: int, obj: dict) -> None:
            data = json.dumps(obj, separators=(",", ":")).encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def _body(self) -> dict:
            n = int(self.headers.get("Content-Length") or 0)
            if n > 128 << 20:
                raise HttpError(413, "too_large", "request too large")
            raw = self.rfile.read(n) if n else b""
            if not raw:
                return {}
            try:
                obj = json.loads(raw.decode("utf-8"))
            except ValueError:
                raise HttpError(400, "bad_request", "body is not JSON")
            if not isinstance(obj, dict):
                raise HttpError(400, "bad_request", "body is not a JSON object")
            return obj

        def _token(self) -> str | None:
            auth = self.headers.get("Authorization") or ""
            return auth[len("Bearer "):] if auth.startswith("Bearer ") else None

        def _dispatch(self, method: str) -> None:
            try:
                path = urllib.parse.urlsplit(self.path).path
                body = self._body() if method in ("POST", "PUT") else {}
                with world.lock:
                    if path.startswith("/fake/"):
                        if self._token() != world.admin_token:
                            raise HttpError(401, "unauthorized", "admin token required")
                        self._reply(200, world.admin(method, path.strip("/").split("/"), body))
                        return
                    member = world.member_of(self._token())
                    if path == "/v1/hello" and method == "GET":
                        self._reply(200, world.hello(member))
                        return
                    m = ROUTE.match(path)
                    if not m:
                        raise HttpError(404, "not_found", "no such call")
                    group, repo = urllib.parse.unquote(m.group(1)), urllib.parse.unquote(m.group(2))
                    ch = world.channel(member, group, repo)
                    kind, uid, idx = m.group(3), m.group(4), m.group(5)
                    if kind is None and method == "GET":
                        self._reply(200, world.state(member, ch))
                    elif kind == "uploads" and uid is None and method == "POST":
                        self._reply(201, world.create_upload(member, ch, body))
                    elif kind == "uploads" and uid is not None and method == "PUT":
                        self._reply(200, world.put_piece(member, ch, urllib.parse.unquote(uid), int(idx), body))
                    elif kind == "pushes" and method == "POST":
                        try:
                            self._reply(200, world.push(member, ch, body))
                        except Refuse as r:
                            self._reply(409, r.body)
                    elif kind == "objects" and method == "POST":
                        self._reply(200, world.objects(member, ch, body))
                    else:
                        raise HttpError(405, "bad_method", "method not allowed")
            except HttpError as e:
                self._reply(e.code, {"error": e.error, "message": e.message})
            except Exception as e:  # a bug in the fake: say so plainly
                self._reply(500, {"error": "internal", "message": "%s: %s" % (type(e).__name__, e)})

        def do_GET(self):  # noqa: N802
            self._dispatch("GET")

        def do_POST(self):  # noqa: N802
            self._dispatch("POST")

        def do_PUT(self):  # noqa: N802
            self._dispatch("PUT")

    return Handler


class ThreadingUnixHTTPServer(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    daemon_threads = True


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--config", required=True)
    ap.add_argument("--listen", default=None, help="host:port on loopback (port 0 picks a free port)")
    ap.add_argument("--unix", default=None, help="Unix socket path")
    ap.add_argument("--port-file", default=None, help="write the endpoint URL here once listening")
    ap.add_argument("--log", default=None)
    a = ap.parse_args()
    with open(a.config) as f:
        world = World(json.load(f))
    log = open(a.log, "a") if a.log else None
    handler = make_handler(world, log)
    if a.unix:
        if os.path.exists(a.unix):
            os.unlink(a.unix)
        srv = ThreadingUnixHTTPServer(a.unix, handler)
        os.chmod(a.unix, 0o600)
        url = "unix:" + a.unix
    else:
        host, _, port = (a.listen or "127.0.0.1:0").rpartition(":")
        if host not in ("127.0.0.1", "localhost"):
            sys.stderr.write("the fake endpoint listens on loopback only\n")
            return 2
        srv = ThreadingHTTPServer((host, int(port)), handler)
        srv.daemon_threads = True
        url = "http://127.0.0.1:%d" % srv.server_address[1]
    if a.port_file:
        tmp = a.port_file + ".tmp"
        with open(tmp, "w") as f:
            f.write(url + "\n")
        os.replace(tmp, a.port_file)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
