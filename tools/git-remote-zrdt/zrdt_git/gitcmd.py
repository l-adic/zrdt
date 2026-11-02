"""The git plumbing the helper uses. Objects leave through ``git cat-file --batch`` and enter
through ``git hash-object -w --no-filters -t <type> --stdin-paths`` (which validates the object
like fsck and recomputes its id); the helper checks every id itself on both sides."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile

from .objects import ObjectError, is_oid, make_raw, object_id, split_raw


class GitError(Exception):
    pass


class Git:
    def __init__(self, git_dir: str | None = None):
        self.env = dict(os.environ)
        if git_dir:
            self.env["GIT_DIR"] = git_dir

    def run(self, args: list[str], input: bytes | None = None, ok_codes=(0,)) -> tuple[int, bytes]:
        p = subprocess.run(["git"] + args, input=input, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           env=self.env)
        if p.returncode not in ok_codes:
            raise GitError("git %s failed: %s" % (" ".join(args[:3]), p.stderr.decode("utf-8", "replace").strip()))
        return p.returncode, p.stdout

    def out(self, args: list[str], input: bytes | None = None) -> str:
        return self.run(args, input)[1].decode("utf-8", "surrogateescape").strip()

    def config_get(self, key: str) -> str | None:
        rc, out = self.run(["config", "--get", key], ok_codes=(0, 1))
        v = out.decode("utf-8", "surrogateescape").strip()
        return v if rc == 0 and v else None

    def git_dir(self) -> str:
        return self.out(["rev-parse", "--absolute-git-dir"])

    def object_format(self) -> str:
        return self.out(["rev-parse", "--show-object-format"])

    def resolve_commit(self, rev: str) -> str:
        rc, out = self.run(["rev-parse", "--verify", "--quiet", "--end-of-options", rev + "^{object}"],
                           ok_codes=(0, 1))
        oid = out.decode().strip()
        if rc != 0 or not is_oid(oid):
            raise GitError("cannot resolve %s" % rev)
        kind = self.out(["cat-file", "-t", oid])
        if kind == "tag":
            raise GitError("%s is an annotated tag; zrdt carries lightweight tags only" % rev)
        if kind != "commit":
            raise GitError("%s is a %s, not a commit" % (rev, kind))
        return oid

    def types(self, ids) -> dict[str, str]:
        """{id: type} for the ids present in the object store."""
        ids = sorted(set(ids))
        if not ids:
            return {}
        _, out = self.run(["cat-file", "--batch-check=%(objectname) %(objecttype)"],
                          input=("\n".join(ids) + "\n").encode())
        have = {}
        for line in out.decode().splitlines():
            parts = line.split()
            if len(parts) == 2 and parts[1] != "missing" and is_oid(parts[0]):
                have[parts[0]] = parts[1]
        return have

    def present(self, ids) -> set[str]:
        return set(self.types(ids))

    def read_raw(self, ids: list[str]) -> dict[str, bytes]:
        """Read objects as raw canonical bytes; check SHA-256(raw) == id for each."""
        ids = sorted(set(ids))
        if not ids:
            return {}
        _, out = self.run(["cat-file", "--batch"], input=("\n".join(ids) + "\n").encode())
        res: dict[str, bytes] = {}
        pos = 0
        for oid in ids:
            nl = out.index(b"\n", pos)
            head = out[pos:nl].decode("ascii", "replace").split()
            if len(head) != 3 or head[0] != oid:
                raise GitError("git cat-file --batch: unexpected reply for %s: %r" % (oid, " ".join(head)))
            kind, size = head[1], int(head[2])
            content = out[nl + 1:nl + 1 + size]
            if len(content) != size or out[nl + 1 + size:nl + 2 + size] != b"\n":
                raise GitError("git cat-file --batch: truncated object %s" % oid)
            pos = nl + 2 + size
            raw = make_raw(kind, content)
            if object_id(raw) != oid:
                raise GitError("object %s in this repository does not hash to its id" % oid)
            res[oid] = raw
        return res

    def write_raw(self, objs: dict[str, bytes]) -> None:
        """Write raw objects with hash-object; check that git computes the same id for each."""
        if not objs:
            return
        by_kind: dict[str, list[tuple[str, bytes]]] = {}
        for oid, raw in sorted(objs.items()):
            if object_id(raw) != oid:
                raise ObjectError("object %s does not hash to its id" % oid, oid)
            kind, content = split_raw(raw)
            by_kind.setdefault(kind, []).append((oid, content))
        tmp = tempfile.mkdtemp(prefix="zrdt-import-")
        try:
            # Blobs first, then trees, then commits, so a reader never sees a dangling reference
            # inside one batch (git does not require it; it keeps partial imports tidy).
            for kind in ("blob", "tree", "commit"):
                items = by_kind.get(kind, [])
                if not items:
                    continue
                paths = []
                for i, (oid, content) in enumerate(items):
                    p = os.path.join(tmp, "%s-%d" % (kind, i))
                    with open(p, "wb") as f:
                        f.write(content)
                    paths.append(p)
                _, out = self.run(["hash-object", "-w", "--no-filters", "-t", kind, "--stdin-paths"],
                                  input=("\n".join(paths) + "\n").encode())
                got = out.decode().split()
                want = [oid for oid, _ in items]
                if got != want:
                    bad = [w for g, w in zip(got, want) if g != w] or want[len(got):]
                    raise GitError("git computed different ids while importing %s objects (first: %s)"
                                   % (kind, bad[0] if bad else "?"))
        finally:
            shutil.rmtree(tmp, ignore_errors=True)

    def is_ancestor(self, a: str, b: str) -> bool:
        rc, _ = self.run(["merge-base", "--is-ancestor", a, b], ok_codes=(0, 1))
        return rc == 0

    def rev_list_objects(self, tips: list[str], exclude: list[str], no_walk: bool = False) -> list[str]:
        """Objects reachable from tips and not from exclude (both commit ids present locally)."""
        if not tips:
            return []
        lines = list(tips) + ["^" + e for e in exclude]
        args = ["rev-list", "--objects", "--stdin"]
        if no_walk:
            args.insert(2, "--no-walk")
        _, out = self.run(args, input=("\n".join(lines) + "\n").encode())
        ids = []
        for line in out.decode("utf-8", "surrogateescape").splitlines():
            oid = line.split(" ", 1)[0]
            if is_oid(oid):
                ids.append(oid)
        return sorted(set(ids))
