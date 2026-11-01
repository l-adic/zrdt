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
the work) and `APP.md` (how the code goes into Signal-Desktop).

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

## 4. The capstone theorems

Several conclusions end in `∨ CollisionIn hash (…)`: "or two different records in the stores
involved have the same hash". That clause is how a hash collision shows up. It is never a
hypothesis. If the main conclusion fails, the theorem hands you the two colliding records. For a
sound hash this branch never happens in practice; for the proofs it means no assumption about the
hash is needed at all.

Status key: **proved** means it builds today with no `sorry` and only the standard axioms;
**to write** means the statement is settled and the proof is planned (see `PLAN.md`).

### (1) Same heads, same chat — `fetched_agree`

If two phones both pass the check and have the same heads, they hold exactly the same set of
messages with the same links.

Why it matters: a few hashes on the screen are enough to compare two people's entire chats.

```lean
theorem fetched_agree (hS : Fetched hash s hs) (hT : Fetched hash t hs) :
    s = t ∨ CollisionIn hash (s ∪ t)
```

**Proved** (`Crdt/Merkle/Integrity.lean`). It rests on `reach_mono_of_complete` (with no
collision, anything reachable in one complete store is reachable in the other) and
`subset_of_fetched` (a tight store is inside any complete store for the same heads).

### (2) Nobody can hide a message from you — `no_silent_exclusion`

If Bob holds a message `m`, and `m` lies behind one of Carol's heads (as seen in Bob's store), and
Carol's store passes the completeness check, then Carol holds `m` too. The server can delay a
message. It cannot make Carol believe she is caught up past a message she never received.

```lean
theorem no_silent_exclusion (hS : Complete hash s hs) (hm : m ∈ t)
    (hreach : Reach hash t hs (hash m)) :
    m ∈ s ∨ CollisionIn hash (s ∪ t)
```

**To write** (proposed statement). It is `reach_mono_of_complete` applied from `t` to `s`, then
`Complete` for `s`.

### (3) An honest phone always passes — `fetched_build`

A phone that accepts records one at a time, each only once its links resolve, is always in a
state the check accepts, and its heads are the correct digest of what it holds.

Why it matters: without this, theorem (1) would be true but unusable; no phone could meet its
hypotheses.

```lean
theorem fetched_build (l : List (Record α H K)) :
    Fetched hash (build hash l) (heads hash (build hash l)) ∨ CollisionIn hash (build hash l)
```

**Proved**. Along the way: `closed_accept` (accepting keeps a store closed) and `heads_insert`
(after accepting a new record, the heads are its hash plus the old heads it did not link):

```lean
theorem heads_insert (hs : Closed hash s) (hr : r ∉ s) (hl : r.links ⊆ digests hash s) :
    heads hash (insert r s) = insert (hash r) (heads hash s \ r.links)
      ∨ CollisionIn hash (insert r s)
```

### (4) Catching up is safe, in any order — `fetched_union` and `strong_eventual_consistency`

Merging two stores that pass the check gives a store that passes the check from the union of
their head sets. And the result of receiving a set of messages depends only on the set, never on
the order or on repeats.

```lean
theorem fetched_union (hS : Fetched hash s hs₁) (hT : Fetched hash t hs₂) :
    Fetched hash (s ∪ t) (hs₁ ∪ hs₂)

theorem strong_eventual_consistency (l₁ l₂ : List (Store α H K))
    (h : l₁.toFinset = l₂.toFinset) : l₁.foldr merge ⊥ = l₂.foldr merge ⊥
```

`fetched_union` is **to write** (no collision clause is needed: both halves follow by induction
on `Reach`). Note that `heads hash (s ∪ t)` may be smaller than `hs₁ ∪ hs₂` when one side has
already linked the other's heads; `Fetched` is stated from `hs₁ ∪ hs₂`, which reaches the same
records. `strong_eventual_consistency` is **proved** (phase 0, re-stated for stores in
`Defs.lean`). A third statement, `build_retry_eq_union` (**to write**), covers the pending
buffer: accepting a closed set of records with retries yields the whole set, in any order.

### (5) The check the phone runs is the check the theorems are about — `check_iff_fetched`

The fast implementation (`ChatStore`, a hash map plus a head set) tracks the specification
exactly. `abs` turns a `ChatStore` into the `Finset` it represents; `Inv` is the invariant that a
well-formed `ChatStore` satisfies.

```lean
theorem abs_accept (h : Inv s) : abs (s.accept r) = accept hashRecord (abs s) r
theorem heads_eq (h : Inv s) : s.heads = heads hashRecord (abs s)
theorem check_iff_fetched (h : Inv s) :
    s.check = .ok ↔ Fetched hashRecord (abs s) (heads hashRecord (abs s))
```

Why it matters: this is the difference between "we proved a model" and "we proved the code".
With these, theorem (1) reads: two phones whose `check` says ok and whose heads match hold the
same history.

**To write**, in `Crdt/Merkle/Refine.lean`, once `Impl.lean` exists. This is the largest proof
task in the project; see section 5.

### (6) Two stories can't be told without it showing — `fork_visible`

If a member sends two different messages as if they were the same message (same author, same
links, different content), then after a merge both are present, with different hashes.

```lean
theorem fork_visible (ha : a ∈ s) (hb : b ∈ t)
    (hauthor : a.author = b.author) (hlinks : a.links = b.links) (hne : a.payload ≠ b.payload) :
    a ∈ s ∪ t ∧ b ∈ s ∪ t ∧ (hash a ≠ hash b ∨ CollisionIn hash (s ∪ t))
```

**To write**. It is short: union never drops a record, and distinct records with equal hashes are
a collision by definition. Its value is the combination with Signal: Signal's signature says who
sent each version, zrdt makes the two versions sit side by side.

### The limit: `withheld_tail_undetectable`

What links alone cannot catch: the server never delivering the *latest* messages, the ones nothing
has replied to yet. A phone holding only the earlier part passes every check.

```lean
-- a concrete countermodel over the toy hash
example : ∃ s t : Store ℕ ℕ Unit, s ⊂ t ∧
    Fetched toyHash s (heads toyHash s) ∧ Fetched toyHash t (heads toyHash t) ∧
    ¬ CollisionIn toyHash t
```

**To write** (take `s = {r0}` and `t = {r0, r1}`). This is why the app has a compare screen: the
remedy for a withheld tail is a second person's heads. Theorem (1) then names the missing digest.

## 5. From proofs to running code

Four layers, top to bottom.

```
  Finset spec        Crdt/Merkle/Defs, Integrity, Chat   — the definitions and theorems above
        │  refinement theorems (Refine.lean): abs, Inv, abs_accept, heads_eq, check_iff_fetched
  ChatStore          Crdt/Merkle/Impl.lean               — Std.HashMap Digest Record + head set
        │  lake build → C
  libzrdt            Crdt/Merkle/Ffi.lean (@[export zrdt_*]) + Lean runtime + vendored SHA-256
        │  FFI
  host app           Signal-Desktop fork (see APP.md)    — transport, storage of the blob, UI
```

**The spec layer** is what section 3 and 4 describe. It runs (`decide`, `#eval`) but slowly: a
`Finset` is a list under the hood.

**The implementation layer** is ordinary Lean code. `ChatStore` holds a `Std.HashMap` from digest
to record and a `Std.HashSet` of heads. Its operations are the ones the app calls: `accept`,
`heads`, `check` (every link resolves, and a walk from the heads visits every entry), `merge`,
`encodeStore`/`decodeStore`, `has`, `reaches`. Here `hash` becomes concrete:
`hashRecord r := sha256 (encode r)`, with `sha256` an opaque function implemented in C and
`encode` a canonical byte encoding written in Lean (`Crdt/Merkle/Encode.lean`).

**Refinement** means: an abstraction function `abs : ChatStore → Store` (the set of records in
the map), an invariant `Inv` (every key is the hash of its value; the head set equals `heads` of
the abstraction), and one theorem per operation saying the implementation's result abstracts to
the spec's result (`abs_accept`, `heads_eq`, `abs_merge`, `decode_encode`, `check_iff_fetched`).
After that, every theorem in section 4 is a theorem about the compiled code, not about a model.
That is the answer to "are the proofs about the code or about a model of it": the code *is* the
Lean, and the only gap between the proved definitions and the shipped binary is the compiler.

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
  received". The phone asks the server, then a peer, to resend it by digest (theorem (2)).
- **A compare screen.** Shows the heads as a QR or word list. Comparing with Bob gives one of:
  identical; Bob has messages you don't (fetch); you have messages Bob doesn't (he's behind);
  both have new messages (merge); or Bob has a message the server won't give you, with its digest
  (the withheld tail).
- **A rejected banner.** On restore or sync, if `check` fails: "This copy of the chat was altered:
  message ·k7f2 is missing", and the copy is not merged (theorems (1), (5)).
- **Checkpoints.** A message whose text is "checkpoint" from someone who is caught up pins down
  the whole chat; its code can be read aloud. "Seen by" is computed from links (Bob has seen it
  if any message of his reaches it), so the server cannot forge it, only withhold it.
- **A fork marker.** Two messages from the same author at the same point are both shown and
  marked "sent as two versions" (theorem (6)).

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
- **Recovery by digest.** Two new message types, `ZrdtResendRequest` and `ZrdtResend`, let a
  phone ask the group for a message it is missing, and let any member answer. The answer is
  verified by hash, so it can come from anyone.
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
