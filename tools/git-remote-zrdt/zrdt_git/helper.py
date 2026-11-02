"""git-remote-zrdt: git's remote-helper protocol for ``zrdt::<group>/<repo>`` remotes.

git calls this helper; it talks to the desktop's local endpoint (ENDPOINT.md); the desktop does
the zrdt work (records, piece stores, zrdtd's checks, Signal). Capabilities: fetch, push, option,
object-format (sha256 only). Objects move as raw canonical bytes, and every id is recomputed here
on the way out (cat-file) and on the way in (before and after hash-object).
"""

from __future__ import annotations

import hashlib
import os
import sys

from .endpoint import Endpoint, EndpointError, Refused, resolve
from .gitcmd import Git, GitError
from .objects import (ObjectError, check_object, group_name_problem, is_oid, object_id,
                      parse_commit, ref_name_problem, repo_name_problem, split_raw)


class Fatal(Exception):
    pass


def parse_url(url: str) -> tuple[str, str]:
    """``zrdt::<group>/<repo>`` (git passes ``<group>/<repo>``) or ``zrdt://<group>/<repo>``."""
    for prefix in ("zrdt::", "zrdt://"):
        if url.startswith(prefix):
            url = url[len(prefix):]
    parts = url.split("/")
    if len(parts) != 2:
        raise Fatal("a zrdt URL is zrdt::<group>/<repo>, got %r" % url)
    group, repo = parts
    problem = group_name_problem(group) or repo_name_problem(repo)
    if problem:
        raise Fatal("bad zrdt URL %r: %s" % (url, problem))
    return group, repo


def short(oid: str | None) -> str:
    return "(none)" if not oid else oid[:12]


def clean(s: object) -> str:
    """A name from the desktop, safe to print on a terminal (no control characters)."""
    return "".join(c if c.isprintable() else "?" for c in str(s))


def short_ref(name: str) -> str:
    for p in ("refs/heads/", "refs/tags/"):
        if name.startswith(p):
            return name[len(p):] if p == "refs/heads/" else "tag " + name[len(p):]
    return name


def check_state(st: dict) -> dict:
    """Validate the shape of a state reply, so nothing unchecked reaches git's protocol stream."""
    if not isinstance(st.get("records"), list) or not isinstance(st.get("refs"), list):
        raise Fatal("the zrdt desktop sent a malformed repository state")
    for r in st["records"]:
        if not is_oid(r.get("record")) or not all(is_oid(o) for o in r.get("objects", [])):
            raise Fatal("the zrdt desktop sent a malformed push record")
        for u in r.get("updates", []):
            if ref_name_problem(u.get("name")) is not None:
                raise Fatal("the zrdt desktop sent a bad ref name %r" % (u.get("name"),))
            if (u.get("new") is not None and not is_oid(u["new"])) or not all(is_oid(v) for v in u.get("old", [])):
                raise Fatal("the zrdt desktop sent a malformed ref update")
    for ref in st["refs"]:
        if ref_name_problem(ref.get("name")) is not None:
            raise Fatal("the zrdt desktop sent a bad ref name %r" % (ref.get("name"),))
        for v in ref.get("values", []):
            if (v.get("value") is not None and not is_oid(v["value"])) or not is_oid(v.get("record")):
                raise Fatal("the zrdt desktop sent a malformed ref value")
    return st


def live_values(st: dict) -> dict[str, list[tuple[str, str]]]:
    """name -> [(value, record)] for live non-delete values, one entry per distinct value
    (the record with the smallest digest names it)."""
    out: dict[str, list[tuple[str, str]]] = {}
    for ref in st["refs"]:
        best: dict[str, str] = {}
        for v in ref.get("values", []):
            if v.get("value") is None:
                continue
            if v["value"] not in best or v["record"] < best[v["value"]]:
                best[v["value"]] = v["record"]
        if best:
            out[ref["name"]] = sorted(best.items())
    return out


def list_lines(st: dict, object_format: bool) -> tuple[list[str], list[str]]:
    """The ``list`` reply lines, and notices for stderr."""
    lines: list[str] = [":object-format sha256"] if object_format else []
    notes: list[str] = []
    plain: list[str] = []
    for name, vals in sorted(live_values(st).items()):
        if len(vals) == 1:
            lines.append("%s %s" % (vals[0][0], name))
            plain.append(name)
        else:
            for value, rec in vals:
                lines.append("%s %s.zrdt-%s" % (value, name, rec[:12]))
            notes.append("%s has %d concurrent values, listed as %s.zrdt-<record>; merge them and push %s"
                         % (short_ref(name), len(vals), short_ref(name), short_ref(name)))
    heads = [n for n in plain if n.startswith("refs/heads/")]
    for cand in ("refs/heads/main", "refs/heads/master"):
        if cand in heads:
            lines.append("@%s HEAD" % cand)
            break
    else:
        if heads:
            lines.append("@%s HEAD" % heads[0])
    not_given = int(st.get("notGiven", 0) or 0)
    if not st["records"] and not_given:
        notes.append("%s/%s has history you were not given (%d push%s). Ask a member to run "
                     "`git zrdt share <branch>`." % (st.get("group", "?"), st.get("repo", "?"), not_given,
                                                     "" if not_given == 1 else "es"))
    for p in st.get("pending", []) or []:
        notes.append("push %s is still arriving (%s pieces missing); fetch again later"
                     % (short(p.get("record")), p.get("missingPieces", "?")))
    return lines, notes


def refusal_text(info: dict, names: list[str]) -> str:
    """One line for git's status report; the reason codes are ENDPOINT.md's."""
    reason = info.get("reason", "")
    msg = clean(info.get("message") or reason)
    branch = short_ref(names[0]) if names else "<branch>"
    if reason == "GATE":
        parts = []
        for s in info.get("seats", []):
            who = clean(s.get("member", "?"))
            if s.get("reason") == "KEY_CHANGED":
                parts.append("%s's safety number changed; pushes stay blocked until the key is verified "
                             "or %s leaves the group" % (who, who))
            else:
                parts.append("%s (new member) has not been given %s" % (who, branch))
        hint = "; run `git zrdt share %s`" % branch if any(s.get("reason") != "KEY_CHANGED"
                                                           for s in info.get("seats", [])) else ""
        return "zrdt: nothing was sent: " + "; ".join(parts or [msg]) + hint
    if reason == "ROOT":
        return ("zrdt: nothing was sent: this push carries a root commit (%s) into a repository with history"
                % short((info.get("objects") or [None])[0]))
    if reason == "NEEDS_CREATE":
        return "zrdt: nothing was sent: you hold no pushes of this repository; to create it, push with -o zrdt.create"
    if reason == "OLD_OBJECT":
        return "zrdt: nothing was sent: %d object(s) were already carried by earlier pushes" % len(info.get("objects", []))
    return "zrdt: nothing was sent: %s (%s)" % (msg, reason)


def oneline(s: str) -> str:
    return " ".join(str(s).split())


class Helper:
    def __init__(self, remote: str, url: str, git: Git | None = None, endpoint: Endpoint | None = None):
        self.remote = remote
        self.url = url
        self.group, self.repo = parse_url(url)
        self.git = git or Git()
        self._ep = endpoint
        self.verbosity = 1
        self.want_format = False
        self.dry_run = False
        self.force = False
        self.atomic = False
        self.push_options: list[str] = []
        self.cas: dict[str, str] = {}

    # -- plumbing ---------------------------------------------------------------------------

    @property
    def ep(self) -> Endpoint:
        if self._ep is None:
            self._ep = resolve(self.git.config_get)
        return self._ep

    def say(self, msg: str, level: int = 1) -> None:
        if self.verbosity >= level:
            sys.stderr.write("zrdt: %s\n" % msg)
            sys.stderr.flush()

    def state(self) -> dict:
        return check_state(self.ep.state(self.group, self.repo))

    def require_sha256(self) -> None:
        try:
            fmt = self.git.object_format()
        except GitError as e:
            raise Fatal(str(e))
        if fmt != "sha256":
            raise Fatal("this repository uses %s object ids; zrdt remotes carry SHA-256 repositories only. "
                        "Create one with `git init --object-format=sha256` (or clone a zrdt remote)." % fmt.upper())

    # -- protocol ---------------------------------------------------------------------------

    def capabilities(self) -> str:
        return "fetch\npush\noption\nobject-format\n\n"

    def option(self, name: str, value: str) -> str:
        if name == "verbosity":
            try:
                self.verbosity = int(value)
            except ValueError:
                return "error bad verbosity"
            return "ok"
        if name in ("progress", "cloning", "followtags", "update-shallow", "check-connectivity"):
            return "ok" if name != "check-connectivity" else "unsupported"
        if name == "object-format":
            # git sends a bare "option object-format" (meaning true) since the capability exists.
            if value in ("", "true"):
                self.want_format = True
                return "ok"
            if value == "sha256":
                return "ok"
            return "error zrdt remotes are SHA-256 only"
        if name == "dry-run":
            self.dry_run = value == "true"
            return "ok"
        if name == "force":
            self.force = value == "true"
            return "ok"
        if name == "atomic":
            self.atomic = value == "true"
            return "ok"
        if name == "push-option":
            self.push_options.append(value)
            return "ok"
        if name == "cas":
            ref, sep, expect = value.partition(":")
            if not sep or (expect and not is_oid(expect)):
                return "error cas needs <ref>:<full object id>"
            self.cas[ref] = expect
            return "ok"
        if name in ("depth", "deepen-since", "deepen-not", "deepen-relative", "unshallow"):
            self.say("%s is not supported: a zrdt remote gives you exactly the history members shared "
                     "with you" % name, 0)
            return "error history depth is fixed by what members shared"
        return "unsupported"

    def list(self, for_push: bool) -> str:
        if for_push:
            self.require_sha256()
        st = self.state()
        lines, notes = list_lines(st, self.want_format)
        for n in notes:
            self.say(n)
        return "".join(l + "\n" for l in lines) + "\n"

    # -- fetch ------------------------------------------------------------------------------

    def fetch(self, wants: list[str]) -> str:
        self.require_sha256()
        st = self.state()
        carried: dict[str, list[dict]] = {}
        for r in st["records"]:
            for o in r.get("objects", []):
                carried.setdefault(o, []).append(r)
        have = self.git.present(carried)
        need = sorted(o for o in carried if o not in have)
        if need:
            self.say("fetching %d object(s) of %d push(es) from the desktop" % (len(need), len(st["records"])))
            got, missing = self.ep.objects(self.group, self.repo, need)
            if missing:
                raise Fatal("the desktop does not have %d object(s) of pushes it listed (first %s); "
                            "fetch again when the pieces arrive" % (len(missing), short(missing[0])))
            for oid in need:
                raw = got.get(oid)
                if raw is None:
                    raise Fatal("the desktop did not send object %s" % short(oid))
                if object_id(raw) != oid:
                    raise Fatal("object %s from the desktop does not hash to its id; nothing was imported" % oid)
                try:
                    kind, content = split_raw(raw)
                    check_object(kind, content)
                except ObjectError as e:
                    raise Fatal("object %s from the desktop was refused: %s; nothing was imported" % (oid, e))
            try:
                self.git.write_raw(got)
            except (GitError, ObjectError) as e:
                raise Fatal(str(e))
        self.update_shallow(st)
        absent = set(wants) - self.git.present(wants)
        if absent:
            raise Fatal("%s is not available from the desktop" % short(sorted(absent)[0]))
        return "\n"

    def update_shallow(self, st: dict) -> None:
        """Recompute this channel's cuts: commits of share records whose parents are absent
        (G-m5: from the applied set, every time). Report a parent missing elsewhere as a gap."""
        commits: dict[str, bool] = {}  # commit id -> carried by a share record
        all_ids = set()
        for r in st["records"]:
            all_ids.update(r.get("objects", []))
        kinds = self.git.types(all_ids)
        raws = self.git.read_raw(sorted(o for o, k in kinds.items() if k == "commit"))
        parents_of: dict[str, list[str]] = {}
        for oid, raw in raws.items():
            kind, content = split_raw(raw)
            if kind == "commit":
                parents_of[oid] = parse_commit(content)[1]
        for r in st["records"]:
            for o in r.get("objects", []):
                if o in parents_of:
                    commits[o] = commits.get(o, False) or bool(r.get("share"))
        parent_ids = {p for ps in parents_of.values() for p in ps}
        have_parents = self.git.present(parent_ids)
        cuts = set()
        for c, is_share in commits.items():
            if any(p not in have_parents for p in parents_of[c]):
                if is_share:
                    cuts.add(c)
                else:
                    self.say("warning: commit %s builds on history you were not given (a gap); "
                             "ask the pusher or a member to share it" % short(c))
        git_dir = self.git.git_dir()
        mine_dir = os.path.join(git_dir, "zrdt")
        mine_path = os.path.join(mine_dir, hashlib.sha256(("%s/%s" % (self.group, self.repo)).encode()).hexdigest()[:16]
                                 + ".shallow")
        shallow_path = os.path.join(git_dir, "shallow")
        mine_old = set(_read_lines(mine_path))
        existing = set(_read_lines(shallow_path))
        new = (existing - mine_old) | cuts
        if new != existing:
            lock = shallow_path + ".lock"
            try:
                fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
            except FileExistsError:
                raise Fatal("%s exists; another git process is updating the shallow file" % lock)
            with os.fdopen(fd, "w") as f:
                f.write("".join(c + "\n" for c in sorted(new)))
            if new:
                os.replace(lock, shallow_path)
            else:
                os.unlink(lock)
                if os.path.exists(shallow_path):
                    os.unlink(shallow_path)
        if cuts or mine_old:
            os.makedirs(mine_dir, exist_ok=True)
            with open(mine_path, "w") as f:
                f.write("".join(c + "\n" for c in sorted(cuts)))
        for c in sorted(cuts - mine_old):
            self.say("%s is a shared commit: you have its files, message and author, not its history" % short(c))

    # -- push -------------------------------------------------------------------------------

    def push(self, cmds: list[tuple[bool, str, str]]) -> str:
        self.require_sha256()
        create = False
        for o in self.push_options:
            if o == "zrdt.create":
                create = True
            else:
                raise Fatal("push option %r is not supported (zrdt knows -o zrdt.create)" % o)
        st = self.state()
        live = {n: [v for v, _ in vals] for n, vals in live_values(st).items()}
        status: dict[str, str] = {}
        order: list[str] = []
        updates: list[dict] = []
        for force, src, dst in cmds:
            order.append(dst)
            force = force or self.force
            problem = ref_name_problem(dst)
            if problem:
                status[dst] = "error %s zrdt: refused ref name: %s" % (dst, problem)
                continue
            try:
                new = self.git.resolve_commit(src) if src else None
            except GitError as e:
                status[dst] = "error %s zrdt: %s" % (dst, oneline(str(e)))
                continue
            olds = live.get(dst, [])
            if dst in self.cas:
                expect = self.cas[dst]
                if (expect == "" and olds) or (expect and olds != [expect]):
                    status[dst] = "error %s stale info" % dst
                    continue
            if new is not None and olds == [new]:
                status[dst] = "ok %s" % dst
                continue
            if new is None and not olds:
                status[dst] = "error %s zrdt: no such ref" % dst
                continue
            forced = False
            bad = None
            for v in olds:
                if not self.git.present([v]):
                    bad = "error %s fetch first" % dst
                    break
                if new is not None and not self.git.is_ancestor(v, new):
                    if not force:
                        bad = "error %s non-fast forward" % dst
                        break
                    forced = True
            if bad:
                status[dst] = bad
                continue
            updates.append({"name": dst, "old": sorted(olds), "new": new, "forced": forced})
            status[dst] = None  # pending
        failed = any(s is not None and not s.startswith("ok ") for s in status.values())
        if self.atomic and failed:
            for u in updates:
                status[u["name"]] = "error %s atomic push failed" % u["name"]
            updates = []
        if updates:
            results = self.publish_updates(st, updates, create)
            status.update(results)
        return "".join(status[d] + "\n" for d in order) + "\n"

    def publish_updates(self, st: dict, updates: list[dict], create: bool) -> dict[str, str]:
        names = [u["name"] for u in updates]
        tips = sorted({u["new"] for u in updates if u["new"]})
        logged = set()
        carried = set()  # what the desktop's table already holds: never re-sent (freshness)
        for r in st["records"]:
            carried.update(r.get("objects", []))
            for u in r.get("updates", []):
                logged.update(u.get("old", []))
                if u.get("new"):
                    logged.add(u["new"])
        exclude = sorted(self.git.present(logged))
        try:
            # rev-list's exclusion is coarse (it can list a blob of an excluded ancestor's tree),
            # so subtract every id a held push carried; those become references.
            ids = [i for i in self.git.rev_list_objects(tips, exclude) if i not in carried]
        except GitError as e:
            return {n: "error %s zrdt: %s" % (n, oneline(str(e))) for n in names}
        request = {"updates": updates, "share": False, "covers": None, "create": create,
                   "dryRun": self.dry_run}
        retried = False
        while True:
            try:
                reply = self.publish(ids, request)
                break
            except Refused as e:
                drop = set(e.info.get("objects", [])) & set(ids)
                if e.reason == "OLD_OBJECT" and not retried and drop:
                    # BUILD_M1 §5: retry once without the ids the desktop names; they become references.
                    self.say("%d object(s) were already carried by earlier pushes; sending without them" % len(drop))
                    ids = [i for i in ids if i not in drop]
                    retried = True
                    continue
                text = refusal_text(e.info, names)
                self.say(text[len("zrdt: "):], 0)
                return {n: "error %s %s" % (n, oneline(text)) for n in names}
            except ObjectError as e:
                text = "zrdt: nothing was sent: object %s cannot be sent: %s" % (short(e.oid), e)
                if "header" in str(e):
                    text += " (signed commits are refused; re-commit without commit.gpgsign)"
                self.say(text[len("zrdt: "):], 0)
                return {n: "error %s %s" % (n, oneline(text)) for n in names}
        for u in updates:
            verb = ("force-pushed" if u["forced"] else "deleted" if u["new"] is None
                    else "created" if not u["old"] else "pushed")
            self.say("%s %s %s -> %s" % (verb, short_ref(u["name"]), short(u["old"][0] if u["old"] else None),
                                         short(u["new"])))
        if self.dry_run:
            self.say("dry run: the desktop checked this push and would publish it")
        else:
            self.say("published push %s to %s (%s); ok means published, not that it won a race"
                     % (short(reply.get("record")), self.group, ", ".join(clean(a) for a in reply.get("audience", []))))
        return {n: "ok %s" % n for n in names}

    def publish(self, ids: list[str], request: dict) -> dict:
        """Read the objects (checking every id), hand them over as pieces, publish the record."""
        try:
            raws = self.git.read_raw(ids)
        except GitError as e:
            raise Fatal(str(e))
        for oid in ids:
            kind, content = split_raw(raws[oid])
            try:
                check_object(kind, content)
            except ObjectError as e:
                raise ObjectError(str(e), oid)
        stream = b"".join(raws[oid] for oid in sorted(ids))
        req = dict(request)
        req["objects"] = sorted(ids)
        req["upload"] = self.ep.upload(self.group, self.repo, stream)
        return self.ep.push(self.group, self.repo, req)


def _read_lines(path: str) -> list[str]:
    try:
        with open(path, "r") as f:
            return [l.strip() for l in f if l.strip()]
    except FileNotFoundError:
        return []


TRACE = bool(os.environ.get("ZRDT_TRACE"))


class _Reader:
    def __init__(self, stream):
        self.stream = stream

    def line(self) -> str | None:
        b = self.stream.readline()
        if not b:
            return None
        s = b.decode("utf-8", "surrogateescape").rstrip("\n")
        if TRACE:
            sys.stderr.write("zrdt-trace: <- %s\n" % s)
        return s


def serve(helper: Helper, inp, out) -> None:
    rd = _Reader(inp)

    def emit(s: str) -> None:
        if TRACE:
            sys.stderr.write("".join("zrdt-trace: -> %s\n" % l for l in s.split("\n")[:-1]))
        out.write(s.encode("utf-8", "surrogateescape"))
        out.flush()

    def handle_option(line: str) -> None:
        _, name, value = (line.split(" ", 2) + ["", ""])[:3]
        emit(helper.option(name, value) + "\n")

    while True:
        line = rd.line()
        if line is None or line == "":
            return
        if line == "capabilities":
            emit(helper.capabilities())
        elif line.startswith("option "):
            handle_option(line)
        elif line in ("list", "list for-push"):
            emit(helper.list(line == "list for-push"))
        elif line.startswith("fetch ") or line.startswith("push "):
            batch = [line]
            while True:
                nxt = rd.line()
                if nxt is None or nxt == "":
                    break
                if nxt.startswith("option "):
                    handle_option(nxt)
                else:
                    batch.append(nxt)
            if line.startswith("fetch "):
                wants = []
                for b in batch:
                    parts = b.split(" ")
                    if len(parts) < 3 or parts[0] != "fetch" or not is_oid(parts[1]):
                        raise Fatal("unexpected fetch line %r" % b)
                    wants.append(parts[1])
                emit(helper.fetch(wants))
            else:
                cmds = []
                for b in batch:
                    if not b.startswith("push "):
                        raise Fatal("unexpected push line %r" % b)
                    spec = b[len("push "):]
                    force = spec.startswith("+")
                    if force:
                        spec = spec[1:]
                    src, sep, dst = spec.partition(":")
                    if not sep:
                        raise Fatal("unexpected push line %r" % b)
                    cmds.append((force, src, dst))
                emit(helper.push(cmds))
        else:
            raise Fatal("unknown command %r from git" % line)


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv if argv is None else argv
    if len(argv) < 2:
        sys.stderr.write("usage: git-remote-zrdt <remote> [<url>]  (git runs this for zrdt::<group>/<repo> remotes)\n")
        return 2
    remote = argv[1]
    url = argv[2] if len(argv) > 2 else argv[1]
    try:
        helper = Helper(remote, url)
        serve(helper, sys.stdin.buffer, sys.stdout.buffer)
        return 0
    except (Fatal, EndpointError, GitError, ObjectError) as e:
        sys.stderr.write("zrdt: %s\n" % e)
        sys.stderr.flush()
        return 128
    except BrokenPipeError:
        return 141
