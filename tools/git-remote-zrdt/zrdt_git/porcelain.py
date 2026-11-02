"""git zrdt: log | status | share for zrdt remotes.

  git zrdt log    [<remote>]                    the push log, forced updates marked
  git zrdt status [<remote>]                    compare code, branches, what you were not given
  git zrdt share  [<remote>] <branch> [--yes] [--dry-run]
                                                share <branch>'s current commit (its files,
                                                message and author; not its history) with the
                                                members that lack it
"""

from __future__ import annotations

import sys

from .endpoint import EndpointError, Refused, resolve
from .gitcmd import Git, GitError
from .helper import Fatal, Helper, check_state, clean, live_values, short, short_ref
from .objects import ObjectError

USAGE = __doc__.split("\n", 2)[2]


def zrdt_remotes(git: Git) -> dict[str, str]:
    rc, out = git.run(["config", "--get-regexp", r"^remote\..*\.url$"], ok_codes=(0, 1))
    res = {}
    for line in out.decode("utf-8", "surrogateescape").splitlines():
        key, _, url = line.partition(" ")
        if url.startswith("zrdt::") or url.startswith("zrdt://"):
            res[key[len("remote."):-len(".url")]] = url
    return res


def pick_remote(git: Git, args: list[str], want_extra: int) -> tuple[str, str, list[str]]:
    """Take an optional leading remote name; return (remote, url, the remaining args)."""
    remotes = zrdt_remotes(git)
    if len(args) > want_extra and args and args[0] in remotes:
        return args[0], remotes[args[0]], args[1:]
    if len(args) > want_extra:
        raise Fatal("%s is not a zrdt remote (zrdt remotes: %s)" % (args[0], ", ".join(sorted(remotes)) or "none"))
    if len(remotes) == 1:
        (name, url), = remotes.items()
        return name, url, args
    if "origin" in remotes:
        return "origin", remotes["origin"], args
    raise Fatal("name the zrdt remote (zrdt remotes: %s)" % (", ".join(sorted(remotes)) or "none"))


def describe(r: dict, u: dict) -> str:
    if r.get("share"):
        verb = "shared"
    elif u.get("new") is None:
        verb = "deleted"
    elif not u.get("old"):
        verb = "created"
    elif u.get("forced"):
        verb = "force-pushed"
    else:
        verb = "pushed"
    if r.get("share"):
        line = "shared %s %s" % (short_ref(u["name"]), short(u.get("new")))
        if r.get("covers"):
            line += " (with %s)" % ", ".join(clean(c) for c in r["covers"])
        return line
    old = ",".join(short(v) for v in u.get("old", [])) or "(none)"
    return "%s %s %s -> %s" % (verb, short_ref(u["name"]), old, short(u.get("new")))


def cmd_log(h: Helper, args: list[str]) -> int:
    st = check_state(h.ep.state(h.group, h.repo))
    recs = sorted(st["records"], key=lambda r: r.get("seq", 0))
    for r in recs:
        for u in r.get("updates", []):
            print("%4s %s %-10s %s" % ("#%s" % r.get("seq", "?"), r["record"][:12], clean(r.get("author", "?")), describe(r, u)))
    if not recs:
        print("(no pushes given to you)")
    ng = int(st.get("notGiven", 0) or 0)
    if ng:
        print("(%d earlier push%s not given to you)" % (ng, "" if ng == 1 else "es"))
    return 0


def cmd_status(h: Helper, args: list[str]) -> int:
    st = check_state(h.ep.state(h.group, h.repo))
    hello = h.ep.hello()
    print("remote %s = zrdt::%s/%s (you are %s)" % (h.remote, h.group, h.repo, clean(hello.get("member", "?"))))
    print("compare code: %s" % clean(st.get("compareCode", "?")))
    print("heads: %s" % (" ".join(d[:12] for d in st.get("heads", [])) or "(none)"))
    print("pushes held: %d; not given to you: %d; still arriving: %d"
          % (len(st["records"]), int(st.get("notGiven", 0) or 0), len(st.get("pending", []) or [])))
    live = live_values(st)
    if live:
        print("branches:")
        for name, vals in sorted(live.items()):
            if len(vals) == 1:
                print("  %-20s %s (push %s)" % (short_ref(name), vals[0][0][:12], vals[0][1][:12]))
            else:
                print("  %-20s DIVERGED: %s" % (short_ref(name), ", ".join("%s (push %s)" % (v[:12], r[:12])
                                                                           for v, r in vals)))
    members = st.get("members", [])
    if members:
        print("members: %s" % ", ".join(clean(m.get("member", "?")) + (" (you)" if m.get("self") else "") for m in members))
    return 0


def cmd_share(h: Helper, args: list[str]) -> int:
    yes = "--yes" in args
    dry = "--dry-run" in args
    rest = [a for a in args if a not in ("--yes", "--dry-run")]
    if len(rest) != 1:
        raise Fatal("usage: git zrdt share [<remote>] <branch> [--yes] [--dry-run]")
    name = rest[0] if rest[0].startswith("refs/") else "refs/heads/" + rest[0]
    h.require_sha256()
    st = check_state(h.ep.state(h.group, h.repo))
    vals = live_values(st).get(name, [])
    if not vals:
        raise Fatal("%s is not on %s" % (short_ref(name), h.remote))
    if len(vals) > 1:
        raise Fatal("%s has %d concurrent values; merge them and push before sharing" % (short_ref(name), len(vals)))
    commit = vals[0][0]
    if not h.git.present([commit]):
        raise Fatal("%s@%s is not in this repository; fetch first" % (short_ref(name), short(commit)))
    ids = h.git.rev_list_objects([commit], [], no_walk=True)
    update = {"name": name, "old": [commit], "new": commit, "forced": False}
    request = {"updates": [update], "share": True, "covers": None, "create": False, "dryRun": True}
    try:
        h.publish(ids, request)
        covers: list[str] = []
    except Refused as e:
        if e.reason != "COVERS_CHANGED":
            raise Fatal("share refused: %s (%s)" % (clean(e.info.get("message", "")), clean(e.reason)))
        covers = [str(c) for c in e.info.get("covers", [])]
    if not covers:
        print("Nobody lacks %s@%s; nothing to share." % (short_ref(name), short(commit)))
        return 0
    print("Share %s@%s with %s: the files of %s, its message and author, and its parent's id; not its history."
          % (short_ref(name), short(commit), ", ".join(clean(c) for c in covers), short(commit)))
    if dry:
        print("(dry run: nothing was shared)")
        return 0
    if not yes:
        if not sys.stdin.isatty():
            raise Fatal("not shared: confirm with --yes")
        sys.stdout.write("Share? [y/N] ")
        sys.stdout.flush()
        if sys.stdin.readline().strip().lower() not in ("y", "yes"):
            print("Not shared.")
            return 1
    request = dict(request, covers=covers, dryRun=False)
    try:
        reply = h.publish(ids, request)
    except Refused as e:
        if e.reason == "COVERS_CHANGED":
            raise Fatal("not shared: the members it would cover changed to %s; run it again"
                        % ", ".join(clean(c) for c in e.info.get("covers", [])))
        raise Fatal("share refused: %s (%s)" % (clean(e.info.get("message", "")), clean(e.reason)))
    print("Shared %s@%s with %s (push %s). Every member of %s sees this share."
          % (short_ref(name), short(commit), ", ".join(clean(c) for c in covers), short(reply.get("record")), h.group))
    return 0


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    if not argv or argv[0] in ("-h", "--help", "help"):
        sys.stdout.write("usage:\n" + USAGE)
        return 0 if argv else 2
    cmd, args = argv[0], argv[1:]
    try:
        git = Git()
        if cmd == "share":
            flags = [a for a in args if a.startswith("--")]
            pos = [a for a in args if not a.startswith("--")]
            remote, url, rest = pick_remote(git, pos, 1)
            h = Helper(remote, url, git=git)
            return cmd_share(h, rest + flags)
        if cmd in ("log", "status"):
            remote, url, rest = pick_remote(git, args, 0)
            h = Helper(remote, url, git=git)
            return cmd_log(h, rest) if cmd == "log" else cmd_status(h, rest)
        sys.stderr.write("git zrdt: unknown command %r\nusage:\n%s" % (cmd, USAGE))
        return 2
    except (Fatal, EndpointError, GitError, ObjectError) as e:
        sys.stderr.write("git zrdt: %s\n" % e)
        return 1
