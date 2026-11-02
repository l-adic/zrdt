# Apps over Signal + zrdt: git sharing and group torrents

Status (2026-11-01): **design only, no code.** Branch `apps`, on join `9637904` (frame protocol
4). The three documents here were written against join `acbd70a` (protocol 3); each plan carries a
protocol caveat at the top. The adversarial review ran, but its findings are not yet folded into
the plans; they are listed, open, at the end of GIT_PLAN.md and TORRENT_PLAN.md.

## The idea

Use a Signal group plus zrdt as a **transport layer**: the group chat's members exchange app data
(not chat messages) as zrdt records, Signal carries the messages and its CDN carries the bulk, and
the Lean daemon `zrdtd` checks everything before it is sent or used. No server of our own. Two apps
on top:
- **git repo sharing**: `git push` / `git fetch` against a remote `zrdt::<group>/<repo>`;
- **group torrent**: share a file or folder with the group; members fetch, check, repair and seed.

The rule carried over from JOIN (R1): a member who joins later gets nothing older unless someone
shares it again on purpose. R2: nothing is signed. R3: Signal's own mechanisms do the transport.

## The build plan

[BUILD_M1.md](BUILD_M1.md) is the plan being built (milestone 1, the mock-server MVP of both apps,
decided 2026-11-02). It overrides the three designs below where they disagree. Its main changes:
- bulk data for both apps goes as piece stores;
- git objects travel raw, with no pack;
- each Signal group has one git channel, and the root rule needs a complete table (G-F1);
- protocol 5 has eleven ops.

It also fixes the lanes and the file ownership.

## The three documents

| Document | What it decides | Chosen design, score |
|---|---|---|
| [TRANSPORT.md](TRANSPORT.md) | The shared layer. A **channel** per (Signal group, app, name), each a zrdt store. The app message rides in a new Content field (205), which stock Desktop and Android drop silently (iOS unverified). Bulk goes as Signal attachments named by a BEP 52 SHA-256 root and checked piece by piece in Lean. `SERVE` is extended to release CDN pointers ("carriers") under a "via" rule. Includes the TCP comparison table (§6). | One design, not scored |
| [GIT_PLAN.md](GIT_PLAN.md) | One push is one record. The bulk is a raw non-thin pack, never a bundle. `zrdtd` recomputes every object id (`CHECK_PACK`) and checks freshness, the **gate** (every seated account already has the base) and a name rule (`CHECK_PUSH`). Refs are a causal multi-value register. Newcomers get only deliberate shares, as shallow cuts. | D2 "zgit" **7.5/10** over D1 "git-remote-zrdt" 6.5/10 (judge's score, before the review) |
| [TORRENT_PLAN.md](TORRENT_PLAN.md) | A torrent is one announcement record A in the group's `bt` channel, plus a closed **piece store**. Each piece (4 to 64 MiB) is a salted record whose opening holds the bytes, and a manifest F lists pieces and files. Repair is JOIN's shipped per-digest `SERVE`, unchanged. | Design 2 "bt/R" **24/30** over design 1 "zbt" 21/30 (judge's score, before the review) |

Review outcome. **Git:** 1 fatal, 7 major and 13 minor open issues. The fatal one: a push with an
empty causal past, which two honest paths produce, sends the whole older history to newcomers.
Breaker 2 asked for a re-score after the fixes. **Torrent:** no fatal break, 5 major and 13 minor
open issues. The most serious is a member removed during the long freeze, then re-added, who gets
the whole torrent.

## What is shared

- **JOIN, as built:** the committed audience (field 201), `SERVE`, the seal, `ACCEPT_VIEW` and the
  relative store.
- **TRANSPORT's Lean base:** `App.lean` (channel ids, a strict app header), `zrdtS4`, and the ops
  `CHANNEL` and `NEW_CHANNEL`.
- **The fork's transport base:** Content 205 send and receive, uploads with a fresh key that skip
  Desktop's 3-day reuse cache, resumable downloads, a pacer, large sealed replies on the CDN, and
  the app socket.
- **Fixes both reviews asked for:**
  - Content 205 must not be saved for Signal's 24-hour retry, which re-sends it to a swapped key.
  - Share and add prompts appear only for adds seen in an authenticated group update, never on a
    key change.
  - Responders need queues and budgets.
- **Not yet shared: the bulk mechanism.** GIT_PLAN carries packs as TRANSPORT blobs, with
  carriers and the via rule. TORRENT_PLAN uses piece stores and recommends them for both apps. See
  question 1.

## What the proofs would be

Nothing is proved yet. Scratch Lean exists only under `/tmp`.
- **Carried over unchanged:** the advertised theorems on join. An app record is an ordinary zrdt
  record, and only the payload in the commitment differs.
- **TRANSPORT:** `opening_bound`, `appOpening_lasting`, `run_accept_app`; for blobs also
  `blobRoot_bound`, `checkPiece_sound`/`_complete`, `serve_blobs` and `assemble_root`. The blob
  theorems are not needed if piece stores are chosen.
- **Git:** `checkPack_rooted`, `checkPack_unsigned`, `checkPush_fresh`, `checkPush_gate`,
  `cuts_are_shares`, `refs_agree`, plus `checkPush_objective` (every member's audit gets the same
  answer). The review shows two of them need new statements:
  - `checkPush_objective` holds only for members that hold every opening in the causal past.
  - `cuts_are_shares` says nothing about file content (squash and revert copy old blobs), so a
    per-object freshness check is needed.
- **Torrent:** `pieces_follow_announcement` is the R1 link: a piece's audience is A's, so the
  shipped `serve_content` gates the bytes. Also `complete_iff`, `assemble_unique`, `btFiles_safe`
  and `btFiles_tile`. Two of them would be advertised in `Api.lean`. The review shows
  `assemble_unique` covers piece bytes, not files on disk: paths that differ only by case or
  Unicode form collide on macOS.
- Comparator, `lake check` and leanchecker run last, only with your approval.

## Recommended build order and effort

Effort is in agent-days, from the plans. It does not include the review fixes.

0. **Now:** only these documents can ship. JOIN, the prerequisite, is built (draft PRs).
1. **Decide** the questions below, at least question 1, then fold the review fixes into the plans
   (about half a day, docs only). Git needs this before any code because of the fatal finding.
2. **Shared base:**
   - TRANSPORT Lean (`App.lean`, channels, `zrdtS4`): 2 to 4 days.
   - The fork's transport base: about 8 days. Shared, so it counts once.
3. **Torrent first** (recommended):
   - Lean (pieces and file table): 5 to 6 days; fork piece stores: 6; CLI: 3; mock harness: 2 to 3.
   - About 5 weeks in all with the base.
   - Demo subset in about 2 weeks: eager publishing, at most 1 GiB, one channel, the CLI, the mock
     server, repair by the author only.
   - Why first:
     - its R1 rests on the shipped `serve_content`;
     - the review found no fatal break;
     - the subset is already defined.
4. **Git second:** about 22.5 days (4.5 weeks) for G1 to G6 on top of the base. The SHA-1 channels
   (G6, 2 days) can wait. The review fixes add work that is not estimated yet. The largest are the
   per-object freshness table, the committed supersedes list and the root rule.

## Honest limits

- **Not peer-to-peer.** Every byte goes through Signal's CDN: one upload, then one download per
  member. Repair means a member re-uploads, sealed to one requester. There is no direct path
  between members.
- **Signal's rate limits.** The open-source defaults are a 1 GB burst, then 1 MB/s of uploads per
  account, and one upload form per 1.2 s. These are shared with the user's own photos. The
  production values and the spam filter are private.
- **CDN lifetime.** Copies last about 30 days; after that, only members' own copies remain.
- **Terms of Service.** Signal's ToS prohibit bulk messaging and auto-messaging. On official
  servers, bulk use risks 428 challenges and action against the account. The plans offer an
  "official" profile (small transfers, every re-upload clicked) and a "private" profile (mock or
  self-hosted server). Demo on the mock server.
- **TCP-like only where true.** True for reliability, retransmission, integrity (SHA-256
  commitments), completeness (the exact missing list) and causal order. Not true for:
  - an ordered byte stream;
  - flow or congestion control;
  - latency bounds;
  - availability;
  - hiding metadata from the server, which sees sizes, timing, and who uploads and downloads.
- **Everyone needs the fork.** Stock clients cannot take part. At most 256 members.
- **TOFU.** The apps inherit Signal's trust on first use. The review found places where both plans
  amplify it (the git share hint, Signal's retry); the fixes are listed.
- **Git specifics.**
  - SHA-256 repositories come first; existing SHA-1 repositories come later.
  - Signed commits are refused.
  - Edited copies of old content cannot be detected.

## Open questions for the user

1. **One bulk mechanism?** (a) Piece stores for both apps. The torrent judge recommends this: one
   R1 argument, the shipped `serve_content`. (b) Git keeps TRANSPORT blobs with carriers and the
   via rule, and the torrent keeps piece stores. That means two mechanisms, and the via rule stays
   host code inside the R1 gate.
2. **Signal's official servers:** offer the apps there at all, capped at about 100 MiB per torrent
   with every re-upload clicked? Or only on the mock and self-hosted servers?
3. **Build order:** torrent first (recommended), git first, or both in parallel after the shared
   base?
4. **Git friction:** do you accept that every add and every key change blocks pushes until a
   member deliberately shares? After the review, a share also needs a committed scope and refuses
   seats whose key changed. The alternative leaks file names and commit ids to seated members who
   never used the repository.
5. **Git SHA-1 channels** (existing repositories; the guarantees read "or a SHA-1 collision"):
   build them after G1, or leave them out?

Smaller per-app questions remain in GIT_PLAN §8 and TORRENT_PLAN §13.
