# zrdt, explained for people

A verified transcript-consistency layer for group chat.

Each message carries the hashes of the messages its sender had already seen. Phones check those
hashes. With that in place, the server in the middle cannot drop, reorder, withhold, or rewrite a
group's history without a phone noticing. The checks are written in Lean 4, proved correct, and
compiled into the code the app runs.

Signal already gives confidentiality (the server can't read messages) and sender authentication
(the server can't forge them). zrdt adds the missing third thing: completeness and consistency of
the history itself. The demo is a Signal-Desktop fork talking to a Signal server we control: an
"evil" build of the mock server that ships in Signal-Desktop's own test suite. It performs the
attacks on cue and the fork catches them. A TLS proxy in front of Signal's staging server is the
fallback for showing the same thing against the real network.

Companion documents: `PLAN.md` (work breakdown, gates, and risks, written for the agents doing
the work), `APP.md` (how the code goes into Signal-Desktop) and `RESTORE_PLAN.md` (getting the
history from anyone and letting the next live message verify it).

---

## 1. The problem

A group chat goes through a server. End-to-end encryption stops the server from reading or forging
messages. It does not stop the server from deciding *which* messages each person gets, or in what
order. Today a server can deliver Alice's message to Bob but not to Carol; deliver two messages in
one order to Bob and the other order to Carol; show one half of the group a different history than
the other half; or simply never deliver the last few messages. Nobody in the group finds out,
because no phone has anything to check against. Delivery receipts don't help: they are messages
too, and the same server carries them.

This gap has a name. The 2015 survey of secure messaging (Unger et al.) calls the missing
property a *global transcript*: everyone sees the same messages in the same order. Schliep,
Kariniemi and Hopper (2017) showed Signal does not provide it. Rösler, Mainka and Schwenk (2018)
showed that in Signal, WhatsApp and Threema, integrity "across all exchanged messages" is not
end-to-end protected. The IETF's successor standard, MLS, says in its own architecture document
that a malicious delivery service "could also reorder messages or provide an inconsistent view to
different users", and that its per-sender counters give loss detection but "this does not provide
complete protection against partitioning"; the proposed fix (AppAck) is still a working-group
draft as of July 2026. A USENIX Security 2026 paper, "Send and Pretend", exploits the gap in
deployed apps. In Signal's own code, the group-message decrypt path silently derives keys for any
skipped message counters (up to `MAX_MESSAGE_KEYS = 2000`) and returns the plaintext; nothing
reports that a gap was seen.

The closest deployed precedent is Keybase chat (2017), where each message carried pointers to
earlier messages: the hash of the earlier message plus the sequence number the server gave it. It
had three limits that zrdt removes. The server still assigned the total order ("clients use
previous pointers to hold the server to previously advertised orderings"). The verifier did not
flag a referenced message that was missing (the code says: "in that case we just check that all
prev pointers to that message are consistent with each other"). And it only ever checked one
client's own view; two members could not compare. zrdt has no server-assigned order, treats a
missing link as a failure, and makes two members' histories comparable with a few hashes.

## 2. The idea in one picture

A message is a *record*: the text, the hashes of the records its author had seen, and the author.
Records form a graph where every arrow is a hash. A phone's state is the *set* of records it
holds. Merging two phones' states is set union, so the order in which things arrive never matters.
The *heads* are the records nothing points to yet: a few hashes that pin down the whole set.

```
  Alice: "lunch?"                 m1
                                   │
  Bob:   "yes"                     m2   links {h(m1)}
                                   │
            ┌──────────────────────┴───────────────────────┐
  Carol: "12:30"   m3  links {h(m2)}          Alice: "where?"   m4  links {h(m2)}
            └──────────────────────┬───────────────────────┘
  Bob:   "the usual, 12:30"        m5   links {h(m3), h(m4)}

  store = {m1, m2, m3, m4, m5}     heads = {h(m5)}
  (before m5 arrived:              heads = {h(m3), h(m4)}  — two people wrote at once)
```

Because every message names what came before it, holding `m5` means holding everything above it.
Two phones with the same heads hold the same set. A server that removes, alters or inserts a
record breaks a hash somewhere, and the phone that checks the hashes sees it.

## 3. Definitions

Everything below is in `Crdt/Merkle/Defs.lean`. Throughout, `α` is the payload type, `H` the
hash type, `K` the author type, and `hash : Record α H K → H` is a *parameter*: a plain function.
Nothing in the proofs assumes it is injective or collision-resistant.

```lean
variable {α H K : Type*} [DecidableEq α] [DecidableEq H] [DecidableEq K]
variable (hash : Record α H K → H)
```

The small examples use a toy hash where a record's hash is its payload (a number), so everything
can be checked by `decide`.

### `Record`

A message plus the hashes of what its author had seen, plus who wrote it.

```lean
structure Record (α H K : Type*) where
  payload : α          -- the message
  links   : Finset H   -- hashes of the records the author had seen (their heads at write time)
  author  : K          -- a claim; Signal verifies it, zrdt does not
```

Example: `r1 = ⟨1, {0}, ()⟩` is a record with payload `1` whose author had seen the record with
hash `0`.

### `Store`

A phone's state: a finite set of records. Merging two stores is set union, so all the phase 0
convergence results apply as they are.

```lean
abbrev Store (α H K : Type*) := Finset (Record α H K)
```

### `CollisionIn`

Two different records in the set `u` have the same hash.

```lean
def CollisionIn (u : Store α H K) : Prop := ∃ x ∈ u, ∃ y ∈ u, x ≠ y ∧ hash x = hash y
```

Why not simply "a collision exists somewhere"? A real hash has a fixed output size and there are
infinitely many possible records, so two colliding records *always* exist, and any theorem that
ends in "or a collision exists" would be trivially true. `CollisionIn` names two records the
phones actually hold. The theorems say: this is true, or here are the two records that collided.
Example: with the toy hash, `CollisionIn hash {⟨0, ∅, ()⟩, ⟨0, {7}, ()⟩}` holds; the two records
differ but both hash to `0`.

### `digests`

The hashes of the records in a store.

```lean
def digests (s : Store α H K) : Finset H := s.image hash
```

### `Closed`

Every link of every record in the store resolves to a record in the store. If you hold a message,
you hold what it was built on.

```lean
def Closed (s : Store α H K) : Prop := ∀ r ∈ s, ∀ d ∈ r.links, ∃ r' ∈ s, hash r' = d
```

Example: `{r0, r1}` with `r0 = ⟨0, ∅, ()⟩` and `r1 = ⟨1, {0}, ()⟩` is closed. `{r1}` alone is
not: it links hash `0` and holds nothing with that hash.

### `heads`

The hashes of the records in the store that no record in the store links to. These are the latest
messages, and what a new message should link.

```lean
def heads (s : Store α H K) : Finset H :=
  (s.filter fun r ↦ ∀ r' ∈ s, hash r ∉ r'.links).image hash
```

Example: `heads hash {r0, r1} = {1}`, since `r1` links `r0`.

### `Reach`

Starting from a set of hashes `hs` and following links of records in `s`, the hashes you can get
to.

```lean
inductive Reach (s : Store α H K) (hs : Finset H) : H → Prop
  | head : d ∈ hs → Reach s hs d
  | link : r ∈ s → Reach s hs (hash r) → d ∈ r.links → Reach s hs d
```

Example: `Reach hash {r0, r1} {1} 0`: from hash `1` you reach `r1`, whose links contain `0`.

### `Complete`, `Tight`, `Fetched`

`Complete`: the store holds a record for every hash reachable from `hs`. Nothing is missing.
`Tight`: every record in the store is reachable from `hs`. Nothing extra was added.
`Fetched`: both. The store is exactly what you get by fetching everything reachable from `hs`.

```lean
def Complete (s : Store α H K) (hs : Finset H) : Prop :=
  ∀ d, Reach hash s hs d → ∃ r ∈ s, hash r = d
def Tight (s : Store α H K) (hs : Finset H) : Prop := ∀ r ∈ s, Reach hash s hs (hash r)
def Fetched (s : Store α H K) (hs : Finset H) : Prop := Complete hash s hs ∧ Tight hash s hs
```

These are the two things a phone checks after a sync or a restore. Example: `{r0, r1}` is
`Fetched` from `{1}`; `{r0, r1, junk}` is not `Tight` from `{1}` if nothing reaches `junk`;
`{r1}` is not `Complete` from `{1}`.

### `accept`

Add a record to the store only if every one of its links resolves. This is the run-time check on
each incoming message.

```lean
def accept (s : Store α H K) (r : Record α H K) : Store α H K :=
  if r.links ⊆ digests hash s then insert r s else s
```

Example: `accept hash {r0} r1 = {r0, r1}`; `accept hash ∅ r1 = ∅` (its link does not resolve).

### `build`

The store a phone has after accepting a list of records one at a time.

```lean
def build (l : List (Record α H K)) : Store α H K := l.foldl (accept hash) ∅
```

Example: `build hash [r0, r1] = {r0, r1}`, but `build hash [r1, r0] = {r0}`: `r1` arrived before
what it links and was dropped. The app keeps such records in a pending buffer and retries; see
theorem 4.

## 4. The theorems

Five statements about the structure, one about the code, and three examples that mark the limits.
Several conclusions end in `∨ CollisionIn hash (…)`: "or two different records in the stores
involved have the same hash". That clause is how a hash collision shows up. It is never a
hypothesis; if the main conclusion fails, the theorem hands you the two colliding records.

Status key: **proved** builds today with no `sorry` and only the standard axioms; **proved in
scratch** is checked against today's build but not yet in the repository; **to prove** means the
statement is settled and the proof is planned (`PLAN.md`).

### (1) Same heads, same chat — `fetched_agree`

If two phones both pass the check and have the same heads, they hold exactly the same set of
messages with the same links. A few hashes on a screen are enough to compare two people's chats.

```lean
theorem fetched_agree (hS : Fetched hash s hs) (hT : Fetched hash t hs) :
    s = t ∨ CollisionIn hash (s ∪ t)
```

**Proved** (`Integrity.lean`), from `reach_mono_of_complete` and `subset_of_fetched`.

### (2) An honest phone always passes — `fetched_build`

A phone that accepts records one at a time, each only once its links resolve, is always in a state
the check accepts, and its heads are the correct digest of what it holds. Without this, (1) would be
true but unusable.

```lean
theorem fetched_build (l : List (Record α H K)) :
    Fetched hash (build hash l) (heads hash (build hash l)) ∨ CollisionIn hash (build hash l)
```

**Proved**. It holds for *any* list of records, which is what makes salvage (4) and the
`CheckedStore` certificate (6) work.

### (3) Catching up is safe — `fetched_union`

Merging two stores that pass the check gives a store that passes the check, from the union of their
head sets. Sync never has to be re-verified from scratch.

```lean
theorem fetched_union (hS : Fetched hash s hs₁) (hT : Fetched hash t hs₂) :
    Fetched hash (s ∪ t) (hs₁ ∪ hs₂)
```

**To prove**; no collision clause is needed. (`heads hash (s ∪ t)` may be smaller than `hs₁ ∪ hs₂`
when one side has linked the other's heads; `Fetched` from `hs₁ ∪ hs₂` reaches the same records.)

### (4) Nothing recoverable is lost — `salvage_maximal`

Take any set of records, in any order, and accept each one as soon as its links are present,
repeating until nothing changes. The result is accept-built (so it passes the check, by (2)), and it
is the *largest* subset that any client could ever have accepted. Everything else is reported, by
hash, as unverifiable.

```lean
def AcceptBuilt (s : Store α H K) : Prop := ∃ l : List _, l.toFinset = s ∧ build hash l = s

theorem salvage_built (u : Store α H K) : AcceptBuilt hash (buildRetry hash u)
theorem salvage_maximal (hs : AcceptBuilt hash s) (hsu : s ⊆ u) : s ⊆ buildRetry hash u
```

**To prove**. Two uses: the pending buffer (messages that arrive before what they link are retried,
and in any arrival order you end with the whole set), and a damaged restore ("3 messages could not be
verified; 1,204 were" is backed by this theorem rather than by a guess).

### (5) A live message confirms exactly what it points at — `confirmed_exact`

Your store and a member's store are both closed, and a message from that member has links that
resolve in both. Then the records reachable from those links in your store are, record for record,
the records reachable from them in the member's store. This is what makes a history imported from
anyone verifiable by the next live message (`RESTORE_PLAN.md`).

```lean
theorem confirmed_exact (hcs : Closed hash s) (hct : Closed hash t)
    (hhs : hs ⊆ digests hash s) (hht : hs ⊆ digests hash t) :
    reachSet hash s hs = reachSet hash t hs ∨
      CollisionIn hash (reachSet hash s hs ∪ reachSet hash t hs)
```

**Proved in scratch**, as (1) applied to `reachSet`, the records reachable from a set of hashes; the
lemma `fetched_reachSet` says that in a closed store the reachable part is itself fetched.

### (6) The code the phone runs is the code the theorems are about — `CheckedStore`

The implementation is a type, `CheckedStore`: a hash map from digest to record, a cached head set,
the chat id, and a proof that the store is accept-built, every key is the hash of its record, every
record belongs to this chat, and the cache is right. The proof field costs nothing at run time. The
only ways to make one are `empty`, `accept`, `merge`, `open` (rebuild a blob by accepting each
record once its links are present) and `salvage`; there is no unchecked store anywhere in the
library or the app. The refinement theorems say each of these computes what the spec defines:

```lean
theorem built_fetched (c : CheckedStore) :
    Fetched hashRecord (abs c) (heads hashRecord (abs c)) ∨ CollisionIn hashRecord (abs c)
theorem abs_accept    : -- per result case: accepted ⇒ abs c' = accept hashRecord (abs c) r, …
theorem abs_merge     : c.merge d = .ok e → abs e = abs c ∪ abs d
theorem heads_eq      : c.heads = heads hashRecord (abs c)
theorem reachSet_iff  : d ∈ c.reachSet hs ↔ (a record of abs c with hash d is reachable from hs)
theorem open_sound    : open b = .ok c → abs c = recordsOf b
theorem open_complete : AcceptBuilt hashRecord (recordsOf b) → ∃ c, open b = .ok c
theorem encode_injective : Function.Injective encode
```

**To prove**, after the implementation exists (`PLAN.md` phase B). This is the largest proof task
in the project and the one that answers "proofs about the code, or about a model?".

### What links alone cannot do — three examples

Each is a concrete countermodel, checked by `decide`, and each is why some part of the app exists.

- **A withheld newest message passes every local check.** A phone holding everything except the
  latest message is in a perfectly consistent state. Remedy: the compare screen (another member's
  heads), after which (1) names the missing digest.
- **A dump whose tail was replaced passes `open`.** A consistent fake tail is a valid history that
  ends somewhere. Remedy: the next live message, by (5); the fake stays unconfirmed.
- **"Withheld" and "never existed" are the same local state.** Two worlds that differ only in
  whether another member holds the record give the phone the identical view. Remedy: ask; the
  referencing sender holds what it linked (`heads_subset_digests`), so its answer is decisive.

### Consequences that are not separate theorems

Some things the design gives are one-line applications of the above and are not advertised as
results: a member who sends two different messages as the same message produces two records with
different hashes that both survive a merge (union keeps everything, and equal hashes on different
records is the definition of a collision); a resent record is accepted only if it hashes to the
requested digest (`accept_unique`); a message reaches a record only if its sender held it
(`reach_implies_held`).

## 5. From proofs to running code

Four layers, top to bottom.

```
  Finset spec        Crdt/Merkle/Defs, Integrity, Chat   — the definitions and theorems above
        │  refinement theorems (Refine.lean), one per constructor and observer
  CheckedStore       Crdt/Merkle/Impl.lean               — hash map + head cache + certificate
        │  lake build → C
  libzrdt            Crdt/Merkle/Ffi.lean (@[export zrdt_*]) + Lean runtime + vendored SHA-256
        │  FFI
  host app           Signal-Desktop fork (see APP.md)    — transport, storage of the blob, UI
```

**The spec layer** is what sections 3 and 4 describe. It runs (`decide`, `#eval`) but slowly: a
`Finset` is a list under the hood.

**The implementation layer** is ordinary Lean code with one dependent type. `CheckedStore` pairs a
raw store (a `Std.HashMap` from digest to record, a `Std.HashSet` of heads, the chat id) with a
proof that it is accept-built, chat-bound and correctly cached. The constructors `empty`, `accept`,
`merge`, `open` and `salvage` are the only producers, so the proof is maintained by construction and
nothing in the library ever handles an unchecked store. `open` is the checker: it decodes the
records and accepts each one once its links are present (a linear worklist); if it consumes
everything, the order it found is the certificate, otherwise the leftovers are the salvage report.
Here `hash` becomes concrete: `hashRecord r := sha256 (encode r)`, with `sha256` implemented in C and
`encode` a canonical byte encoding written in Lean (`Encode.lean`) that includes the chat id, so a
record from another chat is rejected on arrival.

**Refinement** means: an abstraction function `abs : CheckedStore → Store` (the set of records in
the map) and, for each constructor and observer, a theorem that its result abstracts to the spec's
result (`abs_accept`, `abs_merge`, `heads_eq`, `reachSet_iff`, `open_sound`, `open_complete`), plus
`built_fetched`, which turns the certificate into the hypothesis every spec theorem needs. After
that, every theorem in section 4 is a theorem about the compiled code, not about a model. That is
the answer to "are the proofs about the code or about a model of it": the code *is* the Lean, and
the only gap between the proved definitions and the shipped binary is the compiler.

**Trusted base**, in full:

- The Lean 4 compiler and runtime (Lean to C, memory management).
- The C compiler.
- The vendored SHA-256 implementation.
- The FFI glue: the few C functions that marshal bytes in and out.
- The host passing the right bytes in and storing the blob the library gives back. If it corrupts
  the blob, `check` on reload catches it, the same way a tampered server is caught.

`encode_injective` (to prove, in `Encode.lean`) says different records encode to different bytes.
With it, a `CollisionIn` in zrdt's sense is a collision of SHA-256 itself, not an encoding bug.

`Test/Differential.lean` runs the spec and the implementation on random traces with `plausible`
(redundant once refinement is proved, cheap during development). `Test/Vectors.lean` holds fixed
inputs and expected hashes so the host can be checked against the library. `Test/Axioms.lean`
pins every main theorem to `[propext, Classical.choice, Quot.sound]` on every build.

## 6. What a user sees

- **A code on every message.** Its hash, shown short. Two people who both have the message and
  compare codes know their chats agree up to that point (theorem (1) with one head). It never
  changes.
- **A gap placeholder.** When a message arrives whose links name something the phone does not
  hold, a placeholder appears where the missing message belongs: "1 message you haven't
  received". The phone asks the member who referenced it, then the group, to resend it by digest (theorem (4)).
- **A compare screen.** Shows the heads as a QR or word list. Comparing with Bob gives one of:
  identical; Bob has messages you don't (fetch); you have messages Bob doesn't (he's behind);
  both have new messages (merge); or Bob has a message the server won't give you, with its digest
  (the withheld tail).
- **A rejected banner.** On restore or sync, if `open` fails: "This copy of the chat was altered:
  message ·k7f2 is missing", and the copy is not merged; "keep what verifies" loads the salvaged
  part (theorems (4), (6)).
- **Checkpoints.** A message whose text is "checkpoint" from someone who is caught up pins down
  the whole chat; its code can be read aloud. "Seen by" is computed from links (Bob has seen it
  if any message of his reaches it), so the server cannot forge it, only withhold it.
- **A fork marker.** Two messages from the same author at the same point are both shown and
  marked "sent as two versions" (a consequence of merge being union; §4).
- **Import and confirmation.** A history imported from a file shows every message grey until a live
  message from a member reaches it; then it turns normal (theorem (5); `RESTORE_PLAN.md`).

Short codes are for glancing. A real comparison needs at least 80 bits (six or more words, or a
QR of the full digest), so that a server cannot grind two histories into the same display.

## 7. Overhead with n members

Almost nothing grows with the group size. The costs grow with how many people write at the same
time, which is usually one or two.

| | Cost | Depends on n? |
|---|---|---|
| Extra bytes per message | 32 B per head the sender links. Turn-taking: 32 B. Burst of k concurrent writers: 32·k B. | Only through k ≤ n; typical k = 1–2 |
| Work to receive a message | One SHA-256 plus one lookup per link. Microseconds. | No |
| Storage per message | 64–96 B (own hash + links) on top of the message itself. 100k messages ≈ 8 MB. | No |
| State to protect | The heads: 32 B each, at most one per member who wrote since everyone last caught up. | ≤ 32·n B; usually 32–64 B |
| Catching up | Swap heads, fetch only the missing messages, one negotiation round trip. | No |
| Full audit of a restore | One pass over the history. 100k messages: well under a second. | No |
| Per-member bookkeeping | None. No acknowledgements, no per-member counters. | No |

Signal already sends a group message once per recipient; zrdt's bytes ride inside that body. For
comparison, vector clocks cost O(n) bytes on every message, always; MLS's proposed AppAck costs
O(n) acknowledgement messages per epoch. Hash links cost O(concurrency) instead. If a very large
group ever has a burst of hundreds of concurrent writers, links per message can be capped (say at
16); the remaining heads get linked by later messages, since linking an older head is allowed.

## 8. Integration plan (overview)

Details, protobuf changes, file paths and the demo script are in `APP.md`.

- **Signal-Desktop fork.** The sender's current heads go into a new field,
  `repeated bytes zrdt_links = 200`, of `DataMessage`. Unmodified clients ignore it.
- **On receive**, after Signal has decrypted and verified the sender, the fork calls
  `libzrdt`'s `accept`. Accepted messages are stored as today; messages whose links do not
  resolve go to a pending buffer and produce a gap placeholder.
- **Recovery by digest.** Three new message types, `ZrdtResendRequest`, `ZrdtResend` and
  `ZrdtNotFound`. The request goes to the member whose message referenced the digest first, then to
  the group; replies go back directly. The answer is verified by hash, so it can come from anyone.
- **Whole-history restore** from any file or member, verified by the next live message:
  `RESTORE_PLAN.md`.
- **The villain.** Signal-Desktop ships a mock Signal server for its own integration tests. Its
  single delivery function is overridden in an `EvilServer` subclass (about fifty lines) that can
  drop, delay, reorder, replay, and partition envelopes per recipient. It still cannot read them.
  Each switch is one attack in the demo. It also provisions the fake "phones" the three desktops
  link to, so no phone numbers are needed and all three run on one machine. A TLS-terminating
  proxy in front of Signal's staging server is the fallback for a demo against the real network.
- **Demo**, three desktops: (1) chat normally; codes match. (2) The server drops a message to
  one member; a gap appears; recovery by digest fills it. (3) The server withholds the latest
  message from one member; the compare screen names the missing digest. (4) A doctored restore is
  rejected, with the digest that failed.
- **Android** is a stretch goal, with the same library through the NDK.

## 9. What is not proved, and not claimed

- **Who wrote a message.** `author` is a claim. Signal's signatures check it; zrdt does not.
- **Confidentiality.** zrdt hides nothing. Signal's encryption does, and zrdt sits inside it.
- **Liveness.** A server can refuse to deliver anything. zrdt detects withholding only when
  something later references the withheld message, or when two members compare heads. It cannot
  make a server deliver.
- **Time.** No theorem says when a message was written. Links give causal order only.
- **Compaction.** Histories only grow. Bounding storage needs a snapshot record and a theorem that
  a compacted history gives the same guarantees; not in scope.
- **The hash.** No theorem says SHA-256 is collision-resistant. Every theorem says "or here are
  two records that collide"; `encode_injective` makes that a collision of SHA-256 itself.
- **Comparator.** Planned for the end of the project, not run yet.

## 10. Sources

- Unger, Dechand, Bonneau, Fahl, Perl, Goldberg, Smith. *SoK: Secure Messaging.* IEEE S&P 2015.
  https://ieee-security.org/TC/SP2015/papers-archived/6949a232.pdf
- Schliep, Kariniemi, Hopper. *Is Bob Sending Mixed Signals?* WPES 2017.
  https://www-users.cs.umn.edu/~hopper/mixed_signals_wpes17.pdf
- Rösler, Mainka, Schwenk. *More is Less: On the End-to-End Security of Group Chats in Signal,
  WhatsApp, and Threema.* IEEE EuroS&P 2018. https://eprint.iacr.org/2017/713
- RFC 9750, *The Messaging Layer Security (MLS) Architecture*, April 2025.
  https://www.rfc-editor.org/rfc/rfc9750.html
- *The Messaging Layer Security (MLS) Extensions*, draft-ietf-mls-extensions (AppAck), July 2026.
  https://datatracker.ietf.org/doc/html/draft-ietf-mls-extensions
- *Send and Pretend: Exploiting Transcript Consistency Issues in End-to-End Encrypted Group
  Chats.* USENIX Security 2026. https://arxiv.org/pdf/2607.27510
- Truong, Terzo, Paterson. *Signal Lost (Integrity): The Signal App is More than the Sum of its
  Protocols.* 2026. https://eprint.iacr.org/2026/484
- libsignal, `rust/protocol/src/group_cipher.rs` (sender-key decrypt path; skipped iterations
  derived silently, `MAX_MESSAGE_KEYS = 2000`, `MAX_FORWARD_JUMPS = 25_000`).
  https://github.com/signalapp/libsignal/blob/main/rust/protocol/src/group_cipher.rs
- Keybase, *Chat Crypto* design document. https://book.keybase.io/docs/chat/crypto
- Keybase client, `go/chat/prev.go` (prev-pointer verification).
  https://github.com/keybase/client/blob/master/go/chat/prev.go
- Kleppmann. *Making CRDTs Byzantine Fault Tolerant.* PaPoC 2022 (hash graphs for CRDTs).
  https://martin.kleppmann.com/papers/bft-crdt-papoc22.pdf
- Miller, Hicks, Katz, Shi. *Authenticated Data Structures, Generically.* POPL 2014 (the
  "correct, or here is a collision" phrasing). https://www.cs.umd.edu/~mwh/papers/gpads.pdf
