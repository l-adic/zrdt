#!/usr/bin/env python3
"""Unit tests: raw objects and their checks, ref names, the helper's list rendering and its
OLD_OBJECT retry, and the fake endpoint's checks (share coverage, BAD_SHARE, ROOT, the register).

  python3 -m unittest discover -s tools/git-remote-zrdt/test -p 'test_*.py'
"""

from __future__ import annotations

import base64
import hashlib
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "fake"))

from zrdt_git import objects as O  # noqa: E402
from zrdt_git.endpoint import Refused  # noqa: E402
from zrdt_git.gitcmd import Git  # noqa: E402
from zrdt_git.helper import Helper, list_lines, refusal_text  # noqa: E402
import fake_endpoint as F  # noqa: E402

Z = "0" * 64
A = "a" * 64
B = "b" * 64

COMMIT = (b"tree " + Z.encode() + b"\nparent " + A.encode() + b"\nauthor A <a@x> 1 +0000\n"
          b"committer A <a@x> 1 +0000\n\nmsg\n")


def tree_entry(mode: bytes, name: bytes, oid: str) -> bytes:
    return mode + b" " + name + b"\0" + bytes.fromhex(oid)


class ObjectsTest(unittest.TestCase):
    def test_raw_roundtrip_and_strict_header(self):
        raw = O.make_raw("blob", b"hi\n")
        self.assertEqual(raw, b"blob 3\0hi\n")
        self.assertEqual(O.split_raw(raw), ("blob", b"hi\n"))
        for bad in (b"blob 03\0hi\n", b"blob 4\0hi\n", b"blob 2\0hi\n", b"blob\0hi", b"blub 3\0hi\n",
                    b"blob -3\0hi\n", b"blob +3\0hi\n"):
            with self.assertRaises(O.ObjectError, msg=bad):
                O.split_raw(bad)
        with self.assertRaisesRegex(O.ObjectError, "tag objects"):
            O.split_raw(b"tag 0\0")

    def test_commit_allow_list(self):
        self.assertEqual(O.parse_commit(COMMIT), (Z, [A]))
        enc = COMMIT.replace(b"\n\nmsg", b"\nencoding ISO-8859-1\n\nmsg")
        self.assertEqual(O.parse_commit(enc), (Z, [A]))
        for header in (b"gpgsig -----BEGIN PGP SIGNATURE-----\n wsBc\n -----END PGP SIGNATURE-----",
                       b"gpgsig-sha256 x", b"mergetag object " + A.encode(), b"x-attest ssh", b"change-id x"):
            bad = COMMIT.replace(b"\n\nmsg", b"\n" + header + b"\n\nmsg")
            with self.assertRaises(O.ObjectError, msg=header):
                O.parse_commit(bad)
        with self.assertRaises(O.ObjectError):  # no committer
            O.parse_commit(b"tree " + Z.encode() + b"\nauthor A <a@x> 1 +0000\n\nm")
        with self.assertRaises(O.ObjectError):  # parent after author
            O.parse_commit(b"tree " + Z.encode() + b"\nauthor A <a@x> 1 +0000\nparent " + A.encode() +
                           b"\ncommitter A <a@x> 1 +0000\n\nm")
        with self.assertRaises(O.ObjectError):  # a SHA-1 id
            O.parse_commit(COMMIT.replace(Z.encode(), b"0" * 40))

    def test_tree_entries(self):
        t = tree_entry(b"100644", b"a.txt", A) + tree_entry(b"40000", b"d", B)
        self.assertEqual(O.parse_tree(t), [("blob", A, b"a.txt"), ("tree", B, b"d")])
        self.assertEqual(O.references("tree", t), [A, B])
        with self.assertRaisesRegex(O.ObjectError, "gitlink"):
            O.parse_tree(tree_entry(b"160000", b"sub", A))
        with self.assertRaises(O.ObjectError):
            O.parse_tree(tree_entry(b"100664", b"a", A))
        with self.assertRaises(O.ObjectError):
            O.parse_tree(tree_entry(b"100644", b"a/b", A))
        with self.assertRaises(O.ObjectError):
            O.parse_tree(tree_entry(b"100644", b"a", A)[:-1])

    def test_check_stream(self):
        raws = sorted([O.make_raw("blob", b"x"), O.make_raw("blob", b"y"), O.make_raw("commit", COMMIT)],
                      key=O.object_id)
        walked = O.check_stream(b"".join(raws))
        self.assertEqual([w[0] for w in walked], [O.object_id(r) for r in raws])
        with self.assertRaisesRegex(O.ObjectError, "increasing"):
            O.check_stream(b"".join(reversed(raws)))
        with self.assertRaisesRegex(O.ObjectError, "increasing"):
            O.check_stream(raws[0] + raws[0])
        with self.assertRaises(O.ObjectError):
            O.check_stream(b"".join(raws)[:-1])

    def test_ids_match_git(self):
        with tempfile.TemporaryDirectory() as d:
            subprocess.run(["git", "init", "-q", "--object-format=sha256", d], check=True)
            env = dict(os.environ, GIT_DIR=os.path.join(d, ".git"))
            for kind, content in (("blob", b"hello\n"), ("commit", COMMIT),
                                  ("tree", tree_entry(b"100644", b"a.txt", A))):
                out = subprocess.run(["git", "hash-object", "--literally", "-t", kind, "--stdin"], input=content,
                                     stdout=subprocess.PIPE, check=True, env=env).stdout.decode().strip()
                self.assertEqual(O.object_id(O.make_raw(kind, content)), out, kind)

    def test_ref_names(self):
        for good in ("refs/heads/main", "refs/heads/feature/x-1", "refs/tags/v1.0", "refs/heads/ünï"):
            self.assertIsNone(O.ref_name_problem(good), good)
        for bad in ("main", "refs/notes/x", "refs/zrdt/x", "refs/heads/main.zrdt-abc", "refs/heads/a..b",
                    "refs/heads/a b", "refs/heads/a\nb", "refs/heads/.x", "refs/heads/x.lock", "refs/heads/x/",
                    "refs/heads/x.", "refs/heads/a@{1}", "refs/heads//x", "refs/heads/a~1", "refs/heads/a:b",
                    "refs/heads/" + "x" * 250, "HEAD"):
            self.assertIsNotNone(O.ref_name_problem(bad), bad)

    def test_url_names(self):
        self.assertIsNone(O.group_name_problem("Camping trip"))
        self.assertIsNotNone(O.group_name_problem(" x"))
        self.assertIsNotNone(O.group_name_problem("a/b"))
        self.assertIsNone(O.repo_name_problem("demo.git"))
        for bad in (".x", "-x", "a/b", "", "x" * 65, "a b"):
            self.assertIsNotNone(O.repo_name_problem(bad), bad)


class ListTest(unittest.TestCase):
    def state(self, refs):
        return {"group": "Code", "repo": "demo", "records": [], "notGiven": 0, "refs": refs}

    def test_single_and_diverged(self):
        st = self.state([
            {"name": "refs/heads/main", "values": [{"value": A, "record": "1" * 64}]},
            {"name": "refs/heads/topic", "values": [{"value": A, "record": "2" * 64}, {"value": B, "record": "3" * 64},
                                                    {"value": B, "record": "4" * 64}]},
        ])
        lines, notes = list_lines(st, True)
        self.assertEqual(lines, [":object-format sha256", A + " refs/heads/main",
                                 A + " refs/heads/topic.zrdt-" + "2" * 12, B + " refs/heads/topic.zrdt-" + "3" * 12,
                                 "@refs/heads/main HEAD"])
        self.assertTrue(any("concurrent" in n for n in notes))

    def test_not_given_notice(self):
        st = self.state([])
        st["notGiven"] = 2
        lines, notes = list_lines(st, False)
        self.assertEqual(lines, [])
        self.assertIn("history you were not given (2 pushes)", notes[0])

    def test_refusal_text(self):
        t = refusal_text({"reason": "GATE", "seats": [{"member": "dave", "reason": "NEW"}]}, ["refs/heads/main"])
        self.assertIn("dave (new member) has not been given main", t)
        self.assertIn("git zrdt share main", t)
        t = refusal_text({"reason": "GATE", "seats": [{"member": "dave", "reason": "KEY_CHANGED"}]},
                         ["refs/heads/main"])
        self.assertIn("safety number changed", t)
        self.assertNotIn("share", t)


class StubEndpoint:
    """Answers OLD_OBJECT once, naming one object, then accepts."""

    def __init__(self, old: str, state: dict):
        self.old = old
        self.st = state
        self.pushes = []

    def state(self, group, repo):
        return self.st

    def upload(self, group, repo, stream):
        return "u%d" % len(self.pushes) if stream else None

    def push(self, group, repo, req):
        self.pushes.append(req)
        if self.old in req["objects"]:
            raise Refused({"status": "refused", "reason": "OLD_OBJECT", "objects": [self.old]})
        return {"status": "ok", "record": "9" * 64, "audience": ["alice"]}


class RetryTest(unittest.TestCase):
    def test_old_object_retry_once(self):
        with tempfile.TemporaryDirectory() as d:
            env = dict(os.environ, GIT_AUTHOR_NAME="a", GIT_AUTHOR_EMAIL="a@x", GIT_COMMITTER_NAME="a",
                       GIT_COMMITTER_EMAIL="a@x")
            subprocess.run(["git", "init", "-q", "--object-format=sha256", d], check=True)
            with open(os.path.join(d, "f"), "w") as f:
                f.write("x\n")
            subprocess.run(["git", "-C", d, "add", "f"], check=True, env=env)
            subprocess.run(["git", "-C", d, "commit", "-qm", "c"], check=True, env=env)
            git = Git(os.path.join(d, ".git"))
            head = git.out(["rev-parse", "HEAD"])
            blob = git.out(["rev-parse", "HEAD:f"])
            ep = StubEndpoint(blob, {"records": [], "refs": []})
            h = Helper("team", "Code/demo", git=git, endpoint=ep)
            h.verbosity = 0
            out = h.push([(False, "HEAD", "refs/heads/main")])
            self.assertEqual(out, "ok refs/heads/main\n\n")
            self.assertEqual(len(ep.pushes), 2)
            self.assertIn(blob, ep.pushes[0]["objects"])
            self.assertNotIn(blob, ep.pushes[1]["objects"])
            self.assertIn(head, ep.pushes[1]["objects"])
            self.assertEqual(ep.pushes[1]["updates"], [{"name": "refs/heads/main", "old": [], "new": head,
                                                        "forced": False}])


class FakeTest(unittest.TestCase):
    """The fake endpoint's checks, driven directly (no HTTP)."""

    def setUp(self):
        self.w = F.World({"accounts": {"alice": "ta", "bob": "tb", "dave": "td"},
                          "groups": {"G": ["alice", "bob"]}})
        self.ch = self.w.channel("alice", "G", "r")

    def push(self, who, objs, updates, **kw):
        objs = sorted(objs, key=O.object_id)
        stream = b"".join(objs)
        up = None
        if stream:
            up = self.w.create_upload(who, self.ch, {"size": len(stream)})["upload"]
            u = self.ch.uploads[up]
            for i in range(u["count"]):
                piece = stream[i * u["pieceSize"]:(i + 1) * u["pieceSize"]]
                self.w.put_piece(who, self.ch, up, i, {"data": base64.b64encode(piece).decode(),
                                                       "sha256": hashlib.sha256(piece).hexdigest()})
        req = dict(upload=up, objects=[O.object_id(o) for o in objs], updates=updates, **kw)
        return self.w.push(who, self.ch, req)

    def history(self):
        blob = O.make_raw("blob", b"one\n")
        tree = O.make_raw("tree", tree_entry(b"100644", b"f", O.object_id(blob)))
        c0 = O.make_raw("commit", b"tree " + O.object_id(tree).encode() + b"\nauthor a <a@x> 1 +0000\n"
                        b"committer a <a@x> 1 +0000\n\nc0\n")
        return blob, tree, c0

    def test_create_root_gate_share(self):
        blob, tree, c0 = self.history()
        c0id = O.object_id(c0)
        main = [{"name": "refs/heads/main", "old": [], "new": c0id, "forced": False}]
        with self.assertRaises(F.Refuse) as r:
            self.push("alice", [blob, tree, c0], main)
        self.assertEqual(r.exception.body["reason"], "NEEDS_CREATE")
        self.assertEqual(self.push("alice", [blob, tree, c0], main, create=True)["status"], "ok")
        # a second root commit into a repository with history: ROOT
        c0b = O.make_raw("commit", c0[c0.index(b"\0") + 1:].replace(b"c0\n", b"c0b\n"))
        with self.assertRaises(F.Refuse) as r:
            self.push("bob", [c0b], [{"name": "refs/heads/x", "old": [], "new": O.object_id(c0b), "forced": False}])
        self.assertEqual(r.exception.body["reason"], "ROOT")
        # dave joins; a child of c0 is gated on him
        self.w.groups["G"].add("dave")
        c1 = O.make_raw("commit", b"tree " + O.object_id(tree).encode() + b"\nparent " + c0id.encode() +
                        b"\nauthor b <b@x> 2 +0000\ncommitter b <b@x> 2 +0000\n\nc1\n")
        upd = [{"name": "refs/heads/main", "old": [c0id], "new": O.object_id(c1), "forced": False}]
        with self.assertRaises(F.Refuse) as r:
            self.push("bob", [c1], upd)
        self.assertEqual(r.exception.body["reason"], "GATE")
        self.assertEqual([s["member"] for s in r.exception.body["seats"]], ["dave"])
        # a share must carry the whole tree
        share = [{"name": "refs/heads/main", "old": [c0id], "new": c0id, "forced": False}]
        with self.assertRaises(F.Refuse) as r:
            self.push("alice", [c0, tree], share, share=True, covers=["dave"])
        self.assertEqual(r.exception.body["reason"], "BAD_SHARE")
        # the covers must be confirmed exactly
        with self.assertRaises(F.Refuse) as r:
            self.push("alice", [blob, tree, c0], share, share=True, covers=None)
        self.assertEqual(r.exception.body["covers"], ["dave"])
        self.assertEqual(self.push("alice", [blob, tree, c0], share, share=True, covers=["dave"])["status"], "ok")
        # now bob's push passes, and dave's view has exactly the share and bob's push
        self.assertEqual(self.push("bob", [c1], upd)["status"], "ok")
        st = self.w.state("dave", self.ch)
        self.assertEqual([r["seq"] for r in st["records"]], [2, 3])
        self.assertEqual(st["notGiven"], 1)
        self.assertEqual([(r["name"], [v["value"] for v in r["values"]]) for r in st["refs"]],
                         [("refs/heads/main", [O.object_id(c1)])])
        got = self.w.objects("dave", self.ch, {"ids": [c0id, O.object_id(blob), O.object_id(c1)]})
        self.assertEqual(len(got["objects"]), 3)

    def test_concurrent_values_and_merge(self):
        blob, tree, c0 = self.history()
        c0id = O.object_id(c0)
        self.push("alice", [blob, tree, c0], [{"name": "refs/heads/main", "old": [], "new": c0id, "forced": False}],
                  create=True)
        c1 = O.make_raw("commit", b"tree " + O.object_id(tree).encode() + b"\nparent " + c0id.encode() +
                        b"\nauthor b <b@x> 2 +0000\ncommitter b <b@x> 2 +0000\n\nc1\n")
        c2 = O.make_raw("commit", c1[c1.index(b"\0") + 1:].replace(b"c1\n", b"c2\n"))
        for who, c in (("alice", c1), ("bob", c2)):  # both replace c0, each without seeing the other
            self.push(who, [c], [{"name": "refs/heads/main", "old": [c0id], "new": O.object_id(c), "forced": False}])
        st = self.w.state("alice", self.ch)
        self.assertEqual(sorted(v["value"] for v in st["refs"][0]["values"]),
                         sorted([O.object_id(c1), O.object_id(c2)]))
        self.push("alice", [], [{"name": "refs/heads/main", "old": sorted([O.object_id(c1), O.object_id(c2)]),
                                 "new": O.object_id(c2), "forced": True}])
        st = self.w.state("bob", self.ch)
        self.assertEqual([v["value"] for v in st["refs"][0]["values"]], [O.object_id(c2)])


if __name__ == "__main__":
    unittest.main()
