#!/usr/bin/env bash
# End-to-end test: git-remote-zrdt and git-zrdt against the fake endpoint (fake/fake_endpoint.py).
# Four members of the Signal group "Code" (Dave joins later) push and fetch zrdt::Code/demo.
# Runs on Linux and macOS (bash 3.2+, git 2.39+, python3 3.8+). KEEP=1 keeps the temp directory.
set -u
HERE=$(cd "$(dirname "$0")/.." && pwd)
PY=${PYTHON:-python3}
T=$(mktemp -d "${TMPDIR:-/tmp}/zrdt-git-e2e.XXXXXX")
T=$(cd "$T" && pwd -P)
PIDS=""
cleanup() {
  for p in $PIDS; do kill "$p" 2>/dev/null; wait "$p" 2>/dev/null; done
  if [ "${KEEP:-0}" = 1 ]; then echo "# kept $T"; else rm -rf "$T"; fi
}
trap cleanup EXIT

export PATH="$HERE:$PATH"
export HOME="$T/home"
mkdir -p "$HOME"
export GIT_CONFIG_GLOBAL="$T/gitconfig" GIT_CONFIG_NOSYSTEM=1
unset GIT_DIR GIT_WORK_TREE ZRDT_TOKEN ZRDT_TOKEN_FILE ZRDT_ENDPOINT
git config --global init.defaultBranch main
git config --global advice.detachedHead false

PASS=0
FAILN=0
pass() { PASS=$((PASS + 1)); printf 'ok %d - %s\n' "$((PASS + FAILN))" "$1"; }
fail() {
  FAILN=$((FAILN + 1)); printf 'not ok %d - %s\n' "$((PASS + FAILN))" "$1"
  if [ -n "${OUT:-}" ]; then printf '%s\n' "$OUT" | sed 's/^/#   /'; fi
}
expect() { local d=$1; shift; if "$@"; then pass "$d"; else fail "$d"; fi; }
has() { case "$1" in *"$2"*) return 0 ;; *) return 1 ;; esac; }
hasnt() { ! has "$1" "$2"; }
rc0_hasnt() { [ "$RC" = 0 ] && hasnt "$1" "$2"; }
eq() { [ -n "$1" ] && [ "$1" = "$2" ]; }   # an empty left side never passes
ne() { [ -n "$2" ] && [ "$1" != "$2" ]; }
# VERBOSE=1 prints every captured output
run_hook() { if [ "${VERBOSE:-0}" = 1 ]; then printf '%s\n' "$OUT" | sed 's/^/#   | /'; fi; }
# run CMD...: capture output in OUT and status in RC
run() { OUT=$("$@" 2>&1); RC=$?; run_hook; }

as() { local who=$1; shift; git -C "$T/$who" "$@"; }
persona() {
  git -C "$T/$1" config user.name "$1"
  git -C "$T/$1" config user.email "$1@example.org"
  git -C "$T/$1" config zrdt.token "tok-$1"
}
N=0
tick() { N=$((N + 1)); export GIT_AUTHOR_DATE="$((1793600000 + N * 60)) +0000" GIT_COMMITTER_DATE="$((1793600000 + N * 60)) +0000"; }
# commit WHO PATH CONTENT MESSAGE
commit() {
  tick
  mkdir -p "$(dirname "$T/$1/$2")"
  printf '%s\n' "$3" > "$T/$1/$2"
  as "$1" add -A && as "$1" commit -q -m "$4"
}
api() { local tok=$1; shift; ZRDT_TOKEN=$tok "$PY" "$HERE/test/call.py" "$@"; }
admin() { api tok-admin "$@"; }
jget() { "$PY" -c 'import json,sys; d=json.load(sys.stdin); print(eval(sys.argv[1]))' "$1"; }
nrecords() { api tok-alice GET /v1/git/Code/demo | jget 'len(d["records"])'; }

cat > "$T/cfg.json" <<'EOF'
{"adminToken": "tok-admin", "pieceSize": 4096, "maxObjectsPerRequest": 5,
 "accounts": {"alice": "tok-alice", "bob": "tok-bob", "carol": "tok-carol", "dave": "tok-dave"},
 "groups": {"Code": ["alice", "bob", "carol"]}}
EOF
start_fake() { # start_fake URLFILE ARGS...
  local f=$1; shift
  "$PY" "$HERE/fake/fake_endpoint.py" --config "$T/cfg.json" --port-file "$f" --log "$T/fake.log" "$@" &
  PIDS="$PIDS $!"
  local i=0
  while [ ! -s "$f" ] && [ $i -lt 100 ]; do sleep 0.1; i=$((i + 1)); done
}
start_fake "$T/url" --listen 127.0.0.1:0
export ZRDT_ENDPOINT
ZRDT_ENDPOINT=$(cat "$T/url")
echo "# zrdt git e2e in $T, endpoint $ZRDT_ENDPOINT, $(git --version), $("$PY" --version 2>&1)"

# --- 0. SHA-1 repositories are refused ----------------------------------------------------------
git init -q "$T/sha1" && persona sha1 && git -C "$T/sha1" config zrdt.token tok-alice
commit sha1 f.txt one "sha1 c0"
run as sha1 push zrdt::Code/demo main
expect "push from a SHA-1 repository is refused" ne "$RC" 0
expect "... saying SHA-256 repositories only" has "$OUT" "SHA-256 repositories only"
expect "... and it created nothing" eq "$(nrecords)" 0

# --- 1. Alice creates the repository -------------------------------------------------------------
git init -q --object-format=sha256 "$T/alice" && persona alice
"$PY" -c "import os,sys; open(sys.argv[1],'wb').write(os.urandom(20000))" "$T/alice/data.bin"
commit alice README.md "demo v0" "c0: start"
mkdir -p "$T/alice/src" && printf 'hello\n' > "$T/alice/src/main.txt" && printf 'demo v1\n' > "$T/alice/README.md"
tick && as alice add -A && as alice commit -q -m "c1: add main"
C0=$(as alice rev-parse HEAD~1)
C1=$(as alice rev-parse HEAD)
as alice remote add team zrdt::Code/demo
run as alice push team main
expect "the first push without -o zrdt.create is refused" ne "$RC" 0
expect "... naming -o zrdt.create" has "$OUT" "zrdt.create"
run as alice push -o zrdt.create team main
expect "alice creates Code/demo with c0 and c1" eq "$RC" 0
expect "... and team/main = c1" eq "$(as alice rev-parse team/main)" "$C1"
expect "... in one record" eq "$(nrecords)" 1

# --- 2. Bob and Carol clone ----------------------------------------------------------------------
for who in bob carol; do
  run git clone -o team -c zrdt.token=tok-$who zrdt::Code/demo "$T/$who"
  expect "$who clones zrdt::Code/demo" eq "$RC" 0
  persona $who
  expect "$who: HEAD = c1" eq "$(as $who rev-parse HEAD)" "$C1"
  expect "$who: the clone is SHA-256" eq "$(as $who rev-parse --show-object-format)" sha256
  expect "$who: the files match (20 kB blob, 5 pieces)" cmp -s "$T/alice/data.bin" "$T/$who/data.bin"
  run as $who fsck --strict --no-progress
  expect "$who: git fsck --strict is clean" eq "$RC" 0
done

# --- 3. Bob force-pushes an amended c1 -----------------------------------------------------------
tick && printf 'hello, amended\n' > "$T/bob/src/main.txt" && as bob commit -q -a --amend -m "c2: amended main"
C2=$(as bob rev-parse HEAD)
run as bob push team main
expect "bob's non-fast-forward push without --force is rejected" ne "$RC" 0
expect "... as non-fast-forward" has "$OUT" "non-fast-forward"
run as bob push --force team main
expect "bob force-pushes c1 -> c2" eq "$RC" 0
for who in alice bob carol; do
  run as $who zrdt log team
  expect "$who's push log shows the force push c1 -> c2" has "$OUT" "bob        force-pushed main ${C1:0:12} -> ${C2:0:12}"
done

# --- 4. Non-fast-forward and fetch-first: git's own check, and the helper's ----------------------
commit alice notes.txt "alice's note" "c1b: alice works on stale c1"
run as alice push team main
expect "alice's push on stale c1 is rejected: fetch first" has "$OUT" "(fetch first)"
as alice fetch -q team
expect "alice's fetch takes the forced update" eq "$(as alice rev-parse team/main)" "$C2"
run as alice push team main
expect "... then her push is rejected: non-fast-forward" has "$OUT" "(non-fast-forward)"
run "$PY" "$HERE/test/drive_helper.py" --git-dir "$T/alice/.git" --url Code/demo refs/heads/main:refs/heads/main
expect "the helper lists main = c2" has "$OUT" "LIST $C2 refs/heads/main"
expect "the helper itself answers 'error refs/heads/main non-fast forward' (git's status string)" has "$OUT" "PUSH error refs/heads/main non-fast forward"
as alice reset -q --hard team/main

# The remote moves between git's list and its push: the helper re-reads and refuses.
as carol fetch -q team && as carol reset -q --hard team/main
commit carol carol.txt "carol's race" "c3r: carol races"
cat > "$T/bob-c3.sh" <<EOF
set -e
export GIT_AUTHOR_DATE="1793609000 +0000" GIT_COMMITTER_DATE="1793609000 +0000"
cd "$T/bob"
printf 'demo v0\n' > README.md   # back to c0's README: that blob was carried by the first push
printf 'bob\n' > bob.txt
git add -A && git commit -q -m "c3: bob restores the README"
git push team main > "$T/bob-c3.out" 2>&1
EOF
run "$PY" "$HERE/test/drive_helper.py" --git-dir "$T/carol/.git" --url Code/demo --between "bash '$T/bob-c3.sh'" refs/heads/main:refs/heads/main
C3=$(as bob rev-parse HEAD)
expect "helper: carol's list said main = c2" has "$OUT" "LIST $C2 refs/heads/main"
expect "helper: after bob's push it answers 'fetch first'" has "$OUT" "PUSH error refs/heads/main fetch first"
expect "bob's c3 was published" eq "$(as bob rev-parse team/main)" "$C3"
BLOB0=$(as alice rev-parse "$C0:README.md")
expect "c3 restores c0's README blob" eq "$(as bob rev-parse "$C3:README.md")" "$BLOB0"
P3=$(api tok-bob GET /v1/git/Code/demo | jget '[r for r in d["records"] if r["seq"] == 3][0]["objects"]')
expect "... which the push references but does not carry again (freshness)" eq "$(has "$P3" "$BLOB0" && echo carried || echo fresh)" fresh
expect "... while it carries c3 itself" has "$P3" "$C3"
as carol fetch -q team
run "$PY" "$HERE/test/drive_helper.py" --git-dir "$T/carol/.git" --url Code/demo refs/heads/main:refs/heads/main
expect "helper: with c3 fetched, carol's c3r is 'non-fast forward'" has "$OUT" "PUSH error refs/heads/main non-fast forward"
run as carol push team main
expect "git: carol's c3r is rejected as non-fast-forward" has "$OUT" "(non-fast-forward)"
as carol reset -q --hard team/main
run as alice push team "$C2:refs/heads/secret"
expect "alice creates branch secret (before dave joins)" eq "$RC" 0

# --- 5. Dave joins; before any share his clone gets nothing older --------------------------------
admin POST /fake/members '{"group":"Code","member":"dave"}' > /dev/null
run git clone -o team -c zrdt.token=tok-dave zrdt::Code/demo "$T/dave"
expect "dave's clone succeeds" eq "$RC" 0
expect "... with the notice 'history you were not given'" has "$OUT" "history you were not given"
persona dave
expect "dave's clone is SHA-256" eq "$(as dave rev-parse --show-object-format)" sha256
expect "dave's clone has no refs" eq "$(as dave for-each-ref | wc -l | tr -d ' ')" 0
expect "dave's clone has no objects" eq "$(as dave count-objects -v | awk '/^(count|in-pack):/ {s += $2} END {print s}')" 0
STATE=$(api tok-dave GET /v1/git/Code/demo)
expect "dave's desktop holds no push and lists no branch" eq "$(printf '%s' "$STATE" | jget 'len(d["records"]), len(d["refs"])')" "(0, 0)"
expect "... and counts 4 pushes not given" eq "$(printf '%s' "$STATE" | jget 'd["notGiven"]')" 4
IDS="\"$C0\",\"$C1\",\"$C2\",\"$C3\",\"$BLOB0\""
expect "asking by id for c0..c3 and an old blob gets all 5 missing" eq "$(api tok-dave POST /v1/git/Code/demo/objects "{\"ids\":[$IDS]}" | jget 'len(d["objects"]), len(d["missing"])')" "(0, 5)"
expect "... while bob gets all 5" eq "$(api tok-bob POST /v1/git/Code/demo/objects "{\"ids\":[$IDS]}" | jget 'len(d["objects"])')" 5

# --- 6. The gate blocks pushes until a member shares ---------------------------------------------
commit carol carol.txt "carol's c4" "c4: carol"
C4=$(as carol rev-parse HEAD)
BEFORE=$(nrecords)
run as carol push team main
expect "carol's push is refused before upload" ne "$RC" 0
expect "... naming dave as a new member" has "$OUT" "dave (new member) has not been given main"
expect "... with the share hint" has "$OUT" "git zrdt share main"
expect "... and nothing was published" eq "$(nrecords)" "$BEFORE"

# --- 7. Alice shares main with Dave --------------------------------------------------------------
as alice fetch -q team
run as alice zrdt share team main --dry-run
expect "share --dry-run states exactly whom it covers" has "$OUT" "Share main@${C3:0:12} with dave: the files of ${C3:0:12}, its message and author, and its parent's id; not its history."
expect "... and shares nothing" eq "$(nrecords)" "$BEFORE"
run as alice zrdt share team main --yes
expect "alice shares main@c3 with dave" has "$OUT" "Shared main@${C3:0:12} with dave"
run as bob zrdt log
expect "everyone's log shows the share" has "$OUT" "alice      shared main ${C3:0:12} (with dave)"

# --- 8. Dave fetches: the shared commit and its files, not its history ---------------------------
run as dave fetch team
expect "dave fetches" eq "$RC" 0
expect "dave: team/main = c3" eq "$(as dave rev-parse team/main)" "$C3"
expect "dave: .git/shallow = c3" eq "$(cat "$T/dave/.git/shallow" 2>/dev/null)" "$C3"
expect "dave: the log of team/main is one commit" eq "$(as dave rev-list --count team/main)" 1
for c in C0 C1 C2; do
  eval "v=\$$c"
  expect "dave does not have $c" ne "$(as dave cat-file -t "$v" 2>/dev/null)" commit
done
T1=$(as alice rev-parse "$C1^{tree}")
expect "dave does not have c1's tree" ne "$(as dave cat-file -t "$T1" 2>/dev/null)" tree
as dave checkout -q -b main team/main
expect "dave has c3's files" cmp -s "$T/alice/data.bin" "$T/dave/data.bin"
run as dave fsck --no-progress
expect "dave: git fsck is clean (shallow)" eq "$RC" 0

# --- 9. Carol's push now passes; Dave fetches it ------------------------------------------------
run as carol push team main
expect "carol's c4 now passes the gate" eq "$RC" 0
as dave fetch -q team
expect "dave: team/main = c4" eq "$(as dave rev-parse team/main)" "$C4"
expect "dave: two commits, still cut at c3" eq "$(as dave rev-list --count team/main) $(cat "$T/dave/.git/shallow")" "2 $C3"
run as dave ls-remote team
expect "dave's ls-remote works and does not list secret" rc0_hasnt "$OUT" "secret"
run as alice push team :secret
expect "deleting secret, a name dave never saw, is refused (the name rule)" has "$OUT" "dave (new member) has not been given secret"

# --- 10. Dave pushes; everyone converges ---------------------------------------------------------
as dave merge -q --ff-only team/main
commit dave dave.txt "dave's first" "c5: dave"
C5=$(as dave rev-parse HEAD)
run as dave push team main
expect "dave pushes c5" eq "$RC" 0
CODES=""
for who in alice bob carol dave; do
  as $who fetch -q team
  expect "$who: team/main = c5" eq "$(as $who rev-parse team/main)" "$C5"
  CODES="$CODES $(as $who zrdt status team | sed -n 's/^compare code: //p')"
done
set -- $CODES
expect "all four compare codes are equal" [ "$1" = "$2" -a "$2" = "$3" -a "$3" = "$4" -a -n "$1" ]
run as dave zrdt log
expect "dave's log starts at the share" has "$OUT" "(4 earlier pushes not given to you)"
expect "... and has no force push in it" rc0_hasnt "$OUT" "force-pushed"
run as alice zrdt log
expect "alice's log has all 7 pushes" eq "$(printf '%s\n' "$OUT" | grep -c '^ *#')" 7

# --- 11. Concurrent values stay visible (explicit old values, BUILD_M1 G-M2) --------------------
run as alice push team "$C4:refs/heads/topic"
expect "alice creates topic = c4" eq "$RC" 0
R=$(api tok-bob POST /v1/git/Code/demo/pushes "{\"updates\":[{\"name\":\"refs/heads/topic\",\"old\":[],\"new\":\"$C5\",\"forced\":false}],\"objects\":[]}")
expect "bob's concurrent create of topic = c5 (not having seen alice's) is published" eq "$(printf '%s' "$R" | jget 'd["status"]')" ok
run as carol ls-remote team
expect "both values are listed as topic.zrdt-<record>" eq "$(printf '%s\n' "$OUT" | grep -c 'refs/heads/topic\.zrdt-')" 2
expect "... and no plain topic" eq "$(printf '%s\n' "$OUT" | grep -c 'refs/heads/topic$')" 0
run as carol zrdt status team
expect "git zrdt status shows topic diverged" has "$OUT" "DIVERGED"
as alice fetch -q team
run as alice push team "$C5:refs/heads/topic"
expect "alice's push of c5 supersedes both values" eq "$RC" 0
run as carol ls-remote team
expect "... now topic = c5 alone" eq "$(printf '%s\n' "$OUT" | grep 'refs/heads/topic')" "$C5	refs/heads/topic"
run as alice push team :topic
expect "alice deletes topic" eq "$RC" 0
run as carol ls-remote team
expect "... and topic is gone" rc0_hasnt "$OUT" "topic"

# --- 12. Every object id is checked on the way in ------------------------------------------------
BLOB5=$(as dave rev-parse "$C5:dave.txt")
admin POST /fake/tamper "{\"group\":\"Code\",\"repo\":\"demo\",\"id\":\"$BLOB5\"}" > /dev/null
run git clone -o team -c zrdt.token=tok-bob zrdt::Code/demo "$T/bob2"
expect "a clone through a desktop serving a corrupted object fails" ne "$RC" 0
expect "... because the object does not hash to its id" has "$OUT" "does not hash to its id"
admin POST /fake/tamper "{\"group\":\"Code\",\"repo\":\"demo\",\"id\":\"$BLOB5\"}" > /dev/null
run git clone -o team -c zrdt.token=tok-bob zrdt::Code/demo "$T/bob3"
expect "with the object restored the clone succeeds" eq "$RC $(as bob3 rev-parse HEAD 2>/dev/null)" "0 $C5"

# --- 13. A changed key blocks pushes, and no share is offered for it -----------------------------
admin POST /fake/key '{"member":"dave"}' > /dev/null
as carol merge -q --ff-only team/main
commit carol carol.txt "carol's c6" "c6: carol"
run as carol push team main
expect "after dave's key change carol's push is refused" ne "$RC" 0
expect "... as a safety-number change" has "$OUT" "dave's safety number changed"
expect "... without a share hint" hasnt "$OUT" "git zrdt share"
run as alice zrdt share team main --yes
expect "a share to dave's changed key is refused" has "$OUT" "KEY_CHANGED"
admin POST /fake/remove '{"group":"Code","member":"dave"}' > /dev/null
run as carol push team main
expect "with dave removed, carol's push passes" eq "$RC" 0

# --- 14. Fetching into a SHA-1 repository is refused; dry runs publish nothing -------------------
run as sha1 fetch zrdt::Code/demo
expect "fetch into a SHA-1 repository is refused" has "$OUT" "SHA-256 repositories only"
commit carol carol.txt "carol's c7" "c7: carol"
BEFORE=$(nrecords)
run as carol push --dry-run team main
expect "push --dry-run succeeds" eq "$RC" 0
expect "... and publishes nothing" eq "$(nrecords)" "$BEFORE"
TREE=$(as carol rev-parse "HEAD^{tree}")
PARENT=$(as carol rev-parse HEAD)
SIGNED=$(printf 'tree %s\nparent %s\nauthor carol <c@x> 1793700000 +0000\ncommitter carol <c@x> 1793700000 +0000\ngpgsig -----BEGIN SSH SIGNATURE-----\n U1NIU0lH\n -----END SSH SIGNATURE-----\n\nsigned\n' "$TREE" "$PARENT" | as carol hash-object -w -t commit --stdin)
run as carol push team "$SIGNED:refs/heads/signed"
expect "a signed commit is refused before anything is sent" has "$OUT" "commit header 'gpgsig' is not allowed"
expect "... and publishes nothing" eq "$(nrecords)" "$BEFORE"
run as carol push --force-with-lease="main:$C1" team main
expect "--force-with-lease against a stale value is rejected (stale info)" has "$OUT" "stale info"
run as carol push --atomic team main HEAD:refs/heads/x.zrdt-y
expect "an atomic push with one refused ref fails" ne "$RC" 0
expect "... names the reserved .zrdt- name" has "$OUT" "reserved for diverged branches"
expect "... and publishes nothing, main included" eq "$(nrecords)" "$BEFORE"

# --- 15. The same over a Unix socket -------------------------------------------------------------
start_fake "$T/url2" --unix "$T/fake.sock"
git init -q --object-format=sha256 "$T/erin" && persona erin && git -C "$T/erin" config zrdt.token tok-alice
commit erin a.txt "over a socket" "s0"
run env ZRDT_ENDPOINT="unix:$T/fake.sock" git -C "$T/erin" push -o zrdt.create zrdt::Code/sock main
expect "push over a Unix-socket endpoint" eq "$RC" 0
run env ZRDT_ENDPOINT="unix:$T/fake.sock" git clone -c zrdt.token=tok-bob zrdt::Code/sock "$T/erin2"
expect "clone over a Unix-socket endpoint" eq "$RC $(as erin2 rev-parse HEAD 2>/dev/null)" "0 $(as erin rev-parse HEAD)"

echo "# $PASS passed, $FAILN failed"
[ "$FAILN" -eq 0 ]
