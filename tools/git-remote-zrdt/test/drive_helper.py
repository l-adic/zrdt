#!/usr/bin/env python3
"""Drive git-remote-zrdt over its stdin/stdout the way git does, with a pause between ``list
for-push`` and ``push`` (to test what the helper itself reports when the remote moved).

  drive_helper.py --git-dir DIR --url Code/demo [--between 'shell cmd'] [+]SRC:DST ...

Prints ``LIST <line>`` for each list line and ``PUSH <line>`` for each push status line.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))


def read_until_blank(p) -> list[str]:
    out = []
    while True:
        line = p.stdout.readline()
        if not line:
            raise SystemExit("helper closed its output early (exit %s)" % p.poll())
        line = line.decode().rstrip("\n")
        if line == "":
            return out
        out.append(line)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--git-dir", required=True)
    ap.add_argument("--url", required=True)
    ap.add_argument("--between", default=None)
    ap.add_argument("specs", nargs="+")
    a = ap.parse_args()
    env = dict(os.environ, GIT_DIR=os.path.abspath(a.git_dir))
    p = subprocess.Popen([sys.executable, os.path.join(HERE, "git-remote-zrdt"), "team", a.url],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, env=env)

    def send(s: str) -> None:
        p.stdin.write(s.encode())
        p.stdin.flush()

    send("capabilities\n")
    caps = read_until_blank(p)
    assert "push" in caps and "object-format" in caps, caps
    send("option object-format true\n")
    assert p.stdout.readline().decode().strip() == "ok"
    send("list for-push\n")
    for line in read_until_blank(p):
        print("LIST " + line)
    sys.stdout.flush()
    if a.between:
        subprocess.run(a.between, shell=True, check=True, stdout=sys.stderr, stderr=sys.stderr)
    send("".join("push %s\n" % s for s in a.specs) + "\n")
    for line in read_until_blank(p):
        print("PUSH " + line)
    send("\n")
    p.stdin.close()
    return p.wait()


if __name__ == "__main__":
    sys.exit(main())
