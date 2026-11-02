# git-remote-zrdt

A git remote helper for `zrdt::<group>/<repo>` remotes: members of a Signal group push to and
fetch from a repository with no git server (GIT_PLAN, BUILD_M1 §4-§5). This directory holds the
helper, the `git zrdt` porcelain, the endpoint spec they speak ([ENDPOINT.md](ENDPOINT.md)), a fake
endpoint, and the tests. SHA-256 repositories only.

```
git remote add team zrdt::Code/demo
git push -o zrdt.create team main    # the first push creates the repository
git clone zrdt::Code/demo            # another member
git push --force team main           # recorded as forced; shows in everyone's log
git zrdt log                         # the push log
git zrdt status                      # compare code, branches, what you were not given
git zrdt share main                  # give a newcomer main's current commit (not its history)
```

## Install and configure

Python 3.8+ standard library and git 2.39+ (tested: Linux git 2.43 / Python 3.12; macOS git 2.54 /
Python 3.9). No build step.

```
ln -s "$PWD/tools/git-remote-zrdt/git-remote-zrdt" ~/.local/bin/   # anything on PATH
ln -s "$PWD/tools/git-remote-zrdt/git-zrdt" ~/.local/bin/
git config --global zrdt.endpoint unix:"$HOME/Library/Application Support/Signal/zrdt-apps.sock"
git config --global zrdt.tokenFile "$HOME/Library/Application Support/Signal/zrdt-apps-git.token"
```

`ZRDT_ENDPOINT`, `ZRDT_TOKEN` and `ZRDT_TOKEN_FILE` override the config (one desktop per demo
member, so a clone can carry its own `zrdt.endpoint` and `zrdt.token`, e.g. `git clone -c
zrdt.token=… zrdt::Code/demo`). `ZRDT_TRACE=1` traces the remote-helper protocol on stderr.

## What it does

- **Capabilities:** `fetch`, `push`, `option`, `object-format` (always `sha256`). Not offered:
  `connect`, `stateless-connect`, `import`, `export` (fast-import would rewrite ids). Depth options
  are refused: a member has exactly the history others gave him.
- **list:** the desktop's register (`refs` in ENDPOINT §4.2). One live value is `refs/heads/n`;
  several are each `refs/heads/n.zrdt-<12 hex of the record>`, and there is no plain `n` until a
  member merges them and pushes `n` (G-M3). HEAD points at `main`, else `master`, else the first
  branch. Names and ids from the desktop are validated before they reach git's protocol stream.
- **push:** for each `push [+]src:dst` it re-reads the state (the remote may have moved since
  `list`) and answers git's own statuses: `fetch first` when a live value is not local, `non-fast
  forward` when one is not an ancestor and the push is not forced, `stale info` for a failed
  `--force-with-lease`. Then it lists the objects to send (`git rev-list --objects` from the new
  tips, excluding every logged value present locally, minus every object a held push already
  carried; those become references), reads them with `git cat-file --batch`, recomputes every id,
  refuses locally what zrdtd would refuse (signed commits, tags, gitlinks), hands the sorted raw
  stream to the desktop in pieces, and publishes. On `OLD_OBJECT` it retries once without the
  named ids. Refusals arrive before anything leaves the machine and are shown as git's `remote
  rejected` with the reason (`dave (new member) has not been given main; run git zrdt share
  main`). `--atomic`, `--dry-run` and `-o zrdt.create` are supported; other push options are
  refused.
- **fetch:** asks the desktop for every object of every push it holds that is missing locally (by
  id), recomputes SHA-256 for each and checks it like zrdtd would; only if all pass does it write
  them with `git hash-object -w --no-filters -t <type> --stdin-paths` (git validates each object
  and recomputes its id; the helper compares). Then it recomputes this channel's cuts: commits of
  share records whose parents are absent go into `.git/shallow` (written with git's lock-file
  convention), cuts whose parents arrived are removed (G-m5), and entries it did not add are kept.
  A missing parent outside a share is reported as a gap.
- **git zrdt share:** shares the branch's current value: the commit and its whole tree, with
  `old = new`. It first asks the desktop whom the share covers and prints exactly that ("Share
  main@… with dave: the files of …, its message and author, and its parent's id; not its
  history."), then publishes with the confirmed list (`--yes`, or a prompt on a terminal). The
  desktop shows its own dialog too, and refuses members whose key changed.

**Why Python and not TypeScript.** BUILD_M1 §5 sketched a Node helper. git runs the helper as a
program on PATH, outside the desktop process: Python 3 is on every macOS (Xcode tools) and Linux
box, needs no build and no `node_modules`, and the helper shares no code with the fork anyway:
every zrdt rule runs in zrdtd behind the endpoint, so the helper is only git plumbing plus JSON.
The demo Mac's Node is not on git's PATH. If the fork later wants to ship the helper inside the app
bundle, the endpoint spec makes it a drop-in rewrite.

## Tests

```
python3 -m unittest discover -s tools/git-remote-zrdt/test -p 'test_*.py'   # 13 unit tests
bash tools/git-remote-zrdt/test/e2e.sh                                       # 107 end-to-end checks
```

`e2e.sh` starts the fake endpoint on a free loopback port (and once on a Unix socket), isolates git
config under a temp HOME, and plays group "Code": Alice creates `zrdt::Code/demo` (a SHA-1 repo and
a push without `-o zrdt.create` are refused first); Bob and Carol clone (5-piece uploads, batched
object fetches, `fsck --strict` clean); Bob force-pushes an amend, and every log shows it; git's
own `fetch first` / `non-fast-forward` and the helper's own answers when the remote moves between
`list` and `push`; Bob's revert references c0's blob without re-sending it; Dave joins and his
clone, his state and his by-id object requests get nothing older; Carol's push is refused by the
gate with nothing published; Alice shares `main`; Dave gets one shallow commit, then Carol's push
passes and Dave pushes too; four equal compare codes; deleting a branch Dave never saw is refused
(the name rule); concurrent values of `topic` are listed as `topic.zrdt-…` until a merge push
supersedes both; a corrupted object from the desktop fails the clone; a key change blocks pushes
without a share hint and refuses the share; a signed commit is refused before anything is sent;
dry runs publish nothing; `--force-with-lease` and `--atomic` behave; and the same works over a
Unix-socket endpoint. `VERBOSE=1` prints every output, `KEEP=1` keeps the temp directory.

## Limits (M1)

- One push carries at most 64 MiB of raw objects (`maxStream`); chains are deferred.
- A fetch fetches every object of every push the member holds (a mirror of what he was given), not
  only what the wanted refs need.
- Lightweight tags only; no `refs/notes/*`; no submodules (gitlinks are refused); no signed
  commits.
- The fake endpoint is a single process playing every member's desktop: everyone sees every
  record's structure at once, so records are linked in one chain. It checks what BUILD_M1 §4.3
  checks, without Signal, CDN, pieces on the wire, or zrdtd.
