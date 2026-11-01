# zrdt, explained for people

A verified transcript-consistency layer for group chat.

Status date: 2026-11-01. Changes marked **[amendment]** follow the review in
`docs/review-2026-11-01/` (`REVIEW.md`, `UPDATE-690ae65.md`, `AMENDMENTS.md`).

Each message carries the hashes of the messages its sender had already seen. Phones check those
hashes. The checks are written in Lean 4, proved correct, and compiled into `zrdtd`, a small
program the app runs beside it. **[amendment]** What that gives (review §4):

> A server cannot make a member's app accept a history with a hole in it: if any later message
> builds on one you lack, you are told and it is fetched. Two members can confirm with one code
> that they hold the same set of messages; once the server splits a group it can never merge it
> back without the gap showing. The server can still delay, hold back the newest messages until
> someone replies or members compare, and deliver concurrent messages in different orders.

Signal already gives confidentiality (the server can't read messages) and sender authentication
(the server can't forge them). zrdt adds the missing third thing: completeness and consistency of
the history itself. **[amendment]** The demo is a Signal-Desktop fork (based on `v8.33.0`, built
and run on a Mac mini) talking to a Signal server we control: an "evil" build of the mock server
that ships in Signal-Desktop's own test suite. It performs the attacks on cue and the fork shows
each one. A TLS proxy in front of Signal's staging server is a stretch goal for showing the same
thing against the real network.

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

**[amendment]** A message is a *record*: the chat id, a *commitment* to the message, the hashes of
the records its author had seen (its *links*), and the author. The commitment is one SHA-256 hash
over the message exactly as Signal sent it (text, timestamp, quote, mentions, attachments:
everything the user sees; minus the zrdt field and the one that holds the group's key) and 32
random bytes picked for that message, the *salt*. So a record pins down its message exactly, but
holds no text. zrdt's store keeps only this structure. The text stays in Signal-Desktop's own
message table, where Desktop's delete, disappearing-message and view-once rules still remove it.
The salt is there because many messages are short and easy to guess: without it, anyone who sees
the hash of a message could test "ok", "yes" or "12:30" against it (review §2.8).

Records form a graph where every arrow is a hash. A phone's state is the *set* of records it
holds. Merging two phones' states is set union, so the order in which things arrive never matters.
The *heads* are the records nothing points to yet: a few hashes that pin down the whole set. In
the picture, each record is shown by the text it commits to.

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
Two phones with the same heads hold the same set. **[amendment]** Removing or changing a record
that a later record links breaks a hash, and the phone that checks the hashes sees it. Removing or
changing the newest record (a head), or adding a made-up record on top, breaks no hash: the history
just ends earlier or later. Those cases show up when members compare codes or when the next live
messages arrive (§4, the limits; update §4.3).

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

**[amendment]** In the app, the payload is the pair (chat id, commitment), a hash is a 32-byte
SHA-256 digest, and the author is the sender's Signal account id (ACI). §4 and §5 show how the
code's records map onto these definitions (`toSpec`).

### `Record`

A message plus the hashes of what its author had seen, plus who wrote it.

```lean
structure Record (α H K : Type*) where
  payload : α          -- the message (in the app: chat id and commitment)
  links   : Finset H   -- hashes of the records the author had seen (their heads at write time)
  author  : K          -- who claims to have written it; see authorConfirmed, §4 (6)
```

**[amendment]** The author field is a claim. Signal checks it only when the record arrives
directly from its author; for a record relayed by someone else, attribution is §4 (6).

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

**[amendment]** The advertised theorems are about `CheckedStore`, the type the shipped program
holds, not about a model. A `CheckedStore` is a sorted map from digest to record, a cached set of
heads, the chat id, and a proof, `Built`, that the store was built correctly (§5). The only ways to
make one are `empty`, `accept`, `merge`, `open` and `salvage`. Three names link it to the
definitions of §3:

- `toSpec r` turns a record of the code into a spec `Record`: the payload is the pair (chat id,
  commitment), and the links become a `Finset`.
- `hashSpec` is the spec-side hash, with `hashSpec (toSpec r) = hashRecord r`, the SHA-256 of the
  record's bytes.
- `abs c` is the set of records `c` holds, as a spec `Store`.

Each advertised statement is proved from a theorem about the plain `Store` of §3. Those spec
theorems (`fetched_agree`, `fetched_of_build`, `fetched_build`, `fetched_union`,
`acceptBuilt_union`, `salvage_built`, `salvage_maximal`, `confirmed_exact`, `reach_implies_held`,
`authorConfirmed_sound`) are the proofs behind them; they are not advertised on their own. The
axiom gate and the README pin the eleven names in `Crdt/Merkle/Api.lean`: the ten
`Zrdt.CheckedStore.*` statements below and `Zrdt.encode_injective`. **[amendment]**

**[amendment]** Below are seven groups of statements about the code, each with the spec theorem
behind it, and four examples that mark the limits. Several conclusions end in
`∨ CollisionIn hashSpec (…)`: "or two different records in the stores involved have the same
hash". That clause is how a hash collision shows up. It is never a hypothesis; if the main
conclusion fails, the theorem hands you the two colliding records. One store on its own never has
a collision (2), so the clause appears only when two stores meet.

**Status (2026-11-01, wave 3)** **[amendment]**: everything in this section is **proved**. It
builds with no `sorry` and only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), and the axiom gate (`Test/Axioms.lean`) pins the eleven advertised names. The
code blocks below are shortened; `Api.lean` has the exact statements, each with an example.
Where an exact statement differs from the plan: `u.map toSpec` is written `specOf u`, the *set*
of `u`'s records (a repeat counts once, order does not matter); `confirmed` asks `c.has h` for
each `h` in `hs`.

### (1) Same heads, same chat — `CheckedStore.agree`

If two phones have the same heads, they hold exactly the same set of messages with the same links.
A few hashes on a screen are enough to compare two people's chats. **[amendment]** The heads are an
`ExtTreeSet`, whose `=` compares contents, so the hypothesis holds whenever the two phones show the
same digests, whatever order their records arrived in. Neither phone has to run a check first:
being a `CheckedStore` is the check.

```lean
theorem CheckedStore.agree (c d) (h : c.heads = d.heads) :
    abs c = abs d ∨ CollisionIn hashSpec (abs c ∪ abs d)
```

Behind it, `fetched_agree`: two stores that both pass the check from the same heads are equal, or
collide. Proved (`Integrity.lean`), from `reach_mono_of_complete` and `subset_of_fetched`.

```lean
theorem fetched_agree (hS : Fetched hash s hs) (hT : Fetched hash t hs) :
    s = t ∨ CollisionIn hash (s ∪ t)
```

### (2) Every store the app holds passes the check — `CheckedStore.fetched`, `no_collision` **[amendment]**

Every `CheckedStore` is exactly what you get by fetching everything reachable from its own heads:
nothing is missing and nothing extra was added. No two different records in it have the same
hash, because it is a map whose keys are unique and each key is its record's hash. That is why
`fetched` needs no collision clause. Without this, (1) would be true but unusable.

```lean
theorem CheckedStore.fetched (c) : Fetched hashSpec (abs c) (heads hashSpec (abs c))
theorem CheckedStore.no_collision (c) : ¬ CollisionIn hashSpec (abs c)
```

Behind it, `fetched_of_build` (`Integrity.lean`): a phone that accepts records one at a time,
each only once its links resolve, is always in a state the check accepts, and its heads are the
correct digest of what it holds. It holds for *any* list of records. `Built` keeps such an order
as its witness (§5), and the same fact makes salvage (4) work. `fetched_build` (`Chat.lean`) is
the same for an accept-built store, which is the form the code's proofs use. **[amendment]**
(name: the list form is `fetched_of_build`)

```lean
theorem fetched_of_build (l : List (Record α H K)) :
    Fetched hash (build hash l) (heads hash (build hash l)) ∨ CollisionIn hash (build hash l)
theorem fetched_build (h : AcceptBuilt hash s) :
    Fetched hash s (heads hash s) ∨ CollisionIn hash s
```

### (3) Accepting and catching up are safe — `CheckedStore.abs_accept`, `abs_merge` **[amendment]**

Each incoming record gets one answer:

- **accepted**: the store grows exactly as the spec's `accept` says, and the digest returned is the
  record's hash;
- **missing** (some links do not resolve; the answer names them), **collision** (a different record
  with the same hash is already there), **wrong chat**, or **too large**: the store is unchanged,
  and the stated reason is true.

Merging two stores gives their union, and the result is again a `CheckedStore`, so (2) holds for
it. Sync never has to be re-verified from scratch. A merge that would bring in a collision or a
record from another chat fails and leaves the store as it was.

```lean
theorem CheckedStore.abs_accept (c) (r) : AcceptMeans c r (c.accept r)
  -- AcceptMeans (Refine.lean), one case per result:
  -- accepted d ⇒ abs c' = accept hashSpec (abs c) (toSpec r) ∧ d = hashRecord r
  -- missing / collision / wrongChat / tooLarge ⇒ c' = c ∧ (the stated reason holds)
theorem CheckedStore.abs_merge (h : c.merge d = .ok e) : abs e = abs c ∪ abs d
```

Behind them, `fetched_union`: merging two stores that pass the check gives a store that passes the
check, from the union of their head sets; and `acceptBuilt_union`: the union of two accept-built
stores (see (4)) is accept-built. Proved (`Chat.lean`); no collision clause is needed, and both
are true as stated even with collisions (update §2). (`heads hash (s ∪ t)` may be smaller than `hs₁ ∪ hs₂`
when one side has linked the other's heads; `Fetched` from `hs₁ ∪ hs₂` reaches the same records.)

```lean
theorem fetched_union (hS : Fetched hash s hs₁) (hT : Fetched hash t hs₂) :
    Fetched hash (s ∪ t) (hs₁ ∪ hs₂)
```

### (4) Opening a copy; nothing recoverable is lost — `CheckedStore.open_iff`, `salvage_spec`, `encode_open` **[amendment]**

`open` loads a saved or received copy of a chat (a *blob*) for chat `g`. It succeeds exactly when:
the bytes decode to chat `g` and a set of records `u`; the sizes are within the limits (fewer than
2^24 records, at most 4096 links each); the records can be accepted one at a time in some order,
each one's links pointing only to records before it; no two different records have the same hash;
and every record belongs to chat `g`. The store it returns holds exactly those records. When it
fails, the answer names the records it could not accept and the link digests that point to
nothing.

```lean
theorem CheckedStore.open_iff : CheckedStore.open g b = .ok c ↔
    ∃ u, decodeBlob b = some (g, u) ∧ WellSized u ∧ AcceptBuilt hashSpec (specOf u) ∧
      ¬ CollisionIn hashSpec (specOf u) ∧ (∀ r ∈ u, r.group = g) ∧ abs c = specOf u ∧
      c.group = g
```

`salvage` is "keep what verifies". It accepts each record as soon as its links are present,
repeating until nothing changes, and reports the rest by digest. The result is the largest set
any client could ever have accepted from those records. If it succeeds on a blob that decodes to
`u`, then `u` had no collision. **[amendment]**

```lean
theorem CheckedStore.salvage_spec (h : salvage g b = .ok s) (hu : decodeBlob b = some (g, u)) :
    ¬ CollisionIn hashSpec (specOf u) ∧ abs s.store = buildRetry hashSpec (specOf u) ∧
      s.store.group = g ∧ (s.dropped = the sorted digests of the rest)
```

Saving a store and opening it again gives back exactly the same store. `=` is exact here because
the maps compare by content.

```lean
theorem CheckedStore.encode_open (c) : CheckedStore.open c.group c.encode = .ok c
```

Behind them, `salvage_built` and `salvage_maximal`. `buildRetry hash u` accepts each record of `u`
once its links are present, until nothing changes. `AcceptBuilt` says some order accepted every
record. Proved (`Chat.lean`; `LoadSpec.lean` and `LoadApi.lean` carry them to the code);
`salvage_maximal` is true as stated, even with collisions, and `u.card` rounds of retrying are
exactly enough (update §2). **[amendment]**

```lean
def AcceptBuilt (s : Store α H K) : Prop := ∃ l : List _, l.toFinset = s ∧ build hash l = s

theorem salvage_built (u : Store α H K) : AcceptBuilt hash (buildRetry hash u)
theorem salvage_maximal (hs : AcceptBuilt hash s) (hsu : s ⊆ u) : s ⊆ buildRetry hash u
```

Two uses: the pending buffer (messages that arrive before what they link are retried, and in any
arrival order you end with the whole set), and a damaged restore ("3 messages could not be
verified; 1,204 were" is backed by this theorem rather than by a guess).

**[amendment]** What `open` catches, and what it does not (update §4.3). It catches a removed or
changed record that another record links, a link to nothing, a changed chat id, and malformed
bytes. It does not catch a removed newest record, an edited newest record, or a made-up record
added on top: each of those is still a consistent history (see the limits below). A copy rewritten
from some point on, with every hash recomputed, also opens. So records loaded by `open` or
`salvage` start as *imported*, not confirmed (§6).

### (5) A live message shows its sender holds what it points at — `CheckedStore.confirmed` **[amendment]**

Your store and a member's store are both closed, and a message from that member has links that
resolve in both. Then the records reachable from those links in your store are, record for record,
the records reachable from them in the member's store, or two records collide. This is what makes
a history imported from anyone verifiable by the next live message (`RESTORE_PLAN.md`).

It says the sender *holds* those records. It does not say who wrote them: a member can link a
record they made up in someone else's name (update §4.4). Who wrote a record is (6).

```lean
theorem CheckedStore.confirmed (c d) (hs : Array Digest)
    (hc : ∀ h ∈ hs, c.has h = true) (hd : ∀ h ∈ hs, d.has h = true) :
    c.reachSet hs = d.reachSet hs ∨ CollisionIn hashSpec (abs c ∪ abs d)
```

Behind it, `confirmed_exact`, and `reach_implies_held` (a message reaches a record only if its
sender held it). Proved (`Chat.lean`), as (1) applied to `reachSet`, the records reachable from a
set of hashes; the lemma `fetched_reachSet` says that in a closed store the reachable part is
itself fetched.

```lean
theorem confirmed_exact (hcs : Closed hash s) (hct : Closed hash t)
    (hhs : hs ⊆ digests hash s) (hht : hs ⊆ digests hash t) :
    reachSet hash s hs = reachSet hash t hs ∨
      CollisionIn hash (reachSet hash s hs ∪ reachSet hash t hs)
```

### (6) Who wrote it — `authorConfirmed`, `CheckedStore.classify_spec` **[amendment]**

The app notes how each record arrived. It is *live* when Signal delivered it with the record's
author as the sender, or this device sent it; *relayed by X* when member X passed it on; and
*imported* when it came from a dump or from "keep what verifies".

A record is **confirmed by its author** (`authorConfirmed`) when a live message from its author
reaches it, and no live message from its author disowns it. To disown a record, an app adds its
digest to a disown list that every later message carries in full, so a member who missed one
message still sees it in the next. Every app disowns any record in its own name
that it did not write (§6, the disown alarm).

`authorConfirmed_sound`, a spec theorem: if an author's app is honest, meaning it disowns every
accepted record in its own name that it did not create, then every author-confirmed record
attributed to that author was created by it, or two records collide. Proved (`Chat.lean`).
`LiveFacts` is what the host knows (which records arrived live, and the disown lists of live
messages); `HonestAuthor` is the "honest app" hypothesis. **[amendment]**

`CheckedStore.classify_spec`: the app's `CLASSIFY` call computes the spec's status for every
record:

- **confirmed by author**;
- **held by X**: a live message from another member X reaches it. Only one name is shown: of
  the members whose live messages reach it, the one with the smallest ACI in byte order, so every
  device shows the same name **[amendment]**;
- **unconfirmed**: nobody has confirmed holding it;
- **not confirmed by author**: the author has a live message written in parallel with it (neither
  reaches the other) and no live message from the author reaches it, or a live message from the
  author disowns it.

The status is decided by links, never by arrival order, so the server cannot cause false
accusations by reordering messages.

The fourth label is `foreignMarked` in `Chat.lean`; when several labels apply, the order is
confirmed, not confirmed, held by, unconfirmed (`status`). **[amendment]**

```lean
theorem CheckedStore.classify_spec (c) (facts) (d) (st) :
    (classify c facts)[d]? = some st ↔
      ∃ r, c.get d = some r ∧ status hashSpec (abs c) (liveOf facts) (toSpec r) = st.toSpec
```

Which records are live is host state, set by the app, not proved (§5, trusted base).

### (7) Different records, different bytes — `encode_injective` **[amendment]**

Two different records never encode to the same bytes. This holds with no size bound, because
every field of a record has a fixed size except the links, which are one array of fixed-size
digests with its count in front. With it, a collision in the theorems above is a collision of
SHA-256 itself, not an encoding bug. Proved (`Crdt/Merkle/EncodeProofs.lean`).

```lean
theorem encode_injective : Function.Injective encode
```

### What links alone cannot do — four examples **[amendment]**

Each is a concrete countermodel over a toy hash, checked by `decide`, and each is why some part of
the app exists.

- **`withheld_tail_undetectable`: a withheld newest message passes every local check.** A phone
  holding everything except the latest message is in a perfectly consistent state. Remedy: the
  next message that links it, or a compare code (another member's heads), after which (1) names
  the missing digest.
- **`tail_replaced_passes_open`: a dump whose tail was replaced passes `open`.** A consistent fake
  tail is a valid history that ends somewhere. The smallest cases are a removed or edited newest
  message, or a made-up message added on top. Remedy: the next live messages, by (5) and (6). No
  other member's live message reaches the fake, so it stays unconfirmed; once its claimed author
  writes without reaching it, it is marked "not confirmed by" that author.
- **`gap_indistinguishable`: "withheld" and "never existed" are the same local state.** Two worlds
  that differ only in whether another member holds the record give the phone the identical view.
  Remedy: ask. The member whose message linked it held it when they sent
  (`heads_subset_digests`), so they can usually answer. But a "not found" is not decisive: the
  server can drop the request or the reply, and an honest member can lack the record (another of
  their devices linked it, or their store was salvaged or erased). So a gap shows that someone is
  inconsistent; it does not prove the server is at fault.
- **`relay_attribution_indistinguishable`: without disown, a relayed record's author cannot be
  checked.** "Alice wrote F and the server dropped it" and "Mallory made up F in Alice's name and
  linked it" give a third member identical views. No rule on the receiving side can tell them
  apart; only something Alice's app sends can. Remedy: `disown` and `authorConfirmed` (6).

### Consequences that are not separate theorems

**[amendment]** Some things the design gives are one-line applications of the above and are not
advertised as results: a member who sends two different messages as the same message produces two
records with different hashes that both survive a merge (union keeps everything, and equal hashes
on different records is the definition of a collision); a resent record is accepted only if it
hashes to the requested digest (`accept_unique`), which shows it is the record that was linked, not
that its claimed author wrote it (whoever linked the digest may have made the record up; see the
fourth example); a message reaches a record only if its sender held it (`reach_implies_held`, a
lemma behind (5)).

## 5. From proofs to running code

Four layers, top to bottom. **[amendment]**

```
  Finset spec    Crdt/Merkle/Defs, Integrity, Chat        — definitions, spec theorems (Mathlib)
        │  Bridge.lean (toSpec, hashSpec, abs), Refine.lean; Api.lean states §4 over CheckedStore
  CheckedStore   core/Zrdt/Store.lean                     — sorted map + heads + Built, no Mathlib
        │  lake build in core/ (package zrdt-core, no Mathlib) → a native program
  zrdtd          core/Zrdtd/Main.lean, Zrdt.Proto.handle  — one process; frames on stdin/stdout
        │  pipes: u32 length ‖ op ‖ body, replies in order
  host app       Signal-Desktop fork (see APP.md)         — transport, SQL rows, provenance, UI
```

**Two packages.** **[amendment]** The Lean code is split so that the shipped program contains no
Mathlib (review §1.1):

- `core/` is the package `zrdt-core`: the library `Zrdt` (the code) and the program `zrdtd`. It
  imports only Lean's own `Init` and `Std`. The Mac that builds the fork builds it in seconds,
  without fetching Mathlib.
- The root package `zrdt` holds the library `Crdt`: the spec, the bridge and every proof, with
  Mathlib. It requires `zrdt-core` by path.
- Nothing under `core/` imports Mathlib or `Crdt`. A gate checks the linked `zrdtd` binary for
  Mathlib start-up code.

Theorems about `Zrdt` definitions live in `Crdt`. They are still theorems about the code that
ships.

**The spec layer** is what sections 3 and 4 describe. It runs (`decide`, `#eval`) but slowly: a
`Finset` is a list under the hood.

**The implementation layer** **[amendment]** is ordinary Lean code with one dependent type, stated
without Mathlib. `CheckedStore` pairs a raw store with a proof, `Built`. The raw store is the chat
id, a `Std.ExtTreeMap` from digest to record, and a `Std.ExtTreeSet` of heads; both keep keys
sorted, and `=` on them compares contents. `Built` says:

- every key is its record's hash;
- every record has the store's chat id;
- the head cache is exactly the keys no record links;
- there is an order of acceptance (newest first) whose members are exactly the stored records;
- the size limits hold.

That every link resolves follows from these. The proof is erased when compiled, so it costs
nothing at run time.

The only constructors are `empty` and `accept`, with its proof `rawAccept_built` (a prototype of
about 100 lines exists, with core and Std only). `merge`, `open` and `salvage` are one worklist,
`acceptAll`, which inserts only through the checked `accept`. A bug in the worklist can only reject
records or leave leftovers; it can never produce an unchecked store. `open` is the checker: it
decodes the records and accepts each one once its links are present. If it consumes everything,
the store is loaded; otherwise the leftovers and the missing digests are the report, and `salvage`
loads what verified. `zrdtd`'s table holds `CheckedStore` values, so every store in the shipped
program is checked by its type.

Here `hash` becomes concrete: `hashRecord r := sha256 (encode r)`. `sha256` is written in Lean,
about 70 lines, and checked against the NIST test vectors with `#guard`. There is no `extern`, no
`opaque` and no C. It runs under `#eval`, and the kernel can check it on small examples
(`decide +kernel`). `encode` is the fixed record format: `"zrdt2" ‖ chat id ‖ commitment ‖ link
count ‖ links (sorted, no duplicates) ‖ author`. The chat id is inside, so a record from another
chat is rejected on arrival (`WRONG_CHAT`). The commitment is computed in Lean too (`COMMIT`), so
the host never hashes anything. **[amendment]** (protocol 2) `COMMIT` also returns the opening
(the salt and the committed bytes), `ACCEPT` returns the record's bytes, and `ACCEPT_RECORD`
accepts a relayed record from its bytes and checks its opening (`BAD_OPENING` if it does not
match). So the host never builds record bytes or openings either.

**`zrdtd`** **[amendment]**. The app does not load Lean into Signal's window. It starts `zrdtd` as a
child process and talks to it in frames over stdin and stdout. One dispatcher,
`Zrdt.Proto.handle`, serves every request (accept, open, salvage, merge, commit, classify, …). If
`zrdtd` exits, the app shows "zrdt unavailable" and marks nothing accepted; on restart it opens
each store again from the saved rows.

**Refinement** **[amendment]**. `Crdt/Merkle/Bridge.lean` defines `toSpec`, `hashSpec` and
`abs : CheckedStore → Store`, and proves that `Built` gives what every spec theorem needs: the
store is accept-built, its head cache is the spec's `heads`, and it has no collision.
`Refine.lean` has one theorem per constructor and observer, saying its result abstracts to the
spec's result. `Api.lean` then states §4 over `CheckedStore`. After that, every advertised theorem
is a theorem about the compiled code, not about a model. That is the answer to "are the proofs
about the code or about a model of it": the code *is* the Lean. The only gap between the proved
definitions and the shipped binary is the Lean compiler and runtime, plus the frame codec and the
protobuf field scan, which are Lean but unproved and small. This is the largest proof task in the
project (`PLAN.md` phase B).

**Trusted base**, in full: **[amendment]**

- The Lean 4 compiler and runtime (Lean to C to machine code, memory management).
- The frame codec and the protobuf field scan in `zrdtd`: Lean, but unproved and small.
- The TypeScript client code in the fork.
- Host duties: setting the provenance flags right (live, relayed, imported), passing the right
  bytes, applying the same scope rule on send and receive, and wording the UI as §6 does.
- The host keeping the rows it is given. If a saved record is lost or changed, `OPEN` on restart
  catches it only when another record links it. A lost or changed newest record, or an extra
  record, passes (§4 (4)).

There is no hand-written C and no external SHA-256.

**[amendment]** `encode_injective` (§4 (7)) says different records encode to different bytes.
With it, a `CollisionIn` in zrdt's sense is a collision of SHA-256 itself, not an encoding bug.

**[amendment]** `Test/Differential.lean` runs the spec and the implementation on random traces
with `plausible` (redundant once refinement is proved, cheap during development).
`Zrdt/Vectors.lean` writes fixed inputs and expected outputs (`vectors.json`). `zrdtd` is run over
them, and the fork's day-1 TypeScript stub, written independently, is compared with `zrdtd` over
the same vectors. `Test/Axioms.lean` pins every advertised theorem to
`[propext, Classical.choice, Quot.sound]` on every build.

## 6. What a user sees

- **A code on every message.** **[amendment]** Its hash, shown short. Two people who both have the
  message and compare codes know their chats agree up to that point (theorem (5) with one digest).
  It never changes.
- **Provenance labels.** **[amendment]** Each message shows how far it is confirmed (theorem (6)):
  - normal: confirmed by its author;
  - "relayed by Bob": it came from Bob, not from its author. Its hash and its content check out,
    but its author has not confirmed it yet;
  - "held by Alice": a live message from Alice (not the author) reaches it;
  - grey: nobody has confirmed holding it;
  - "not confirmed by Bob": Bob, its claimed author, has written a live message in parallel with
    it that does not reach it, or has disowned it.
- **A gap row.** **[amendment]** When a message arrives whose links name something the phone does
  not hold, a row appears where the missing message belongs: "1 message you haven't received".
  The phone asks the member whose message referenced it, 1:1, then the group, to resend it by
  digest; the waiting message is kept until it can be accepted (theorem (4)). The missing message
  appears in place, first as "relayed by Bob". The app then asks its author to send it again; the
  author's copy arrives live, and the message turns normal. A gap shows that someone is
  inconsistent, not that the server is at fault: a member can link a made-up digest, and an
  offline author looks the same.
- **Compare codes.** **[amendment]** "Copy compare code" puts the full sorted set of heads on the
  clipboard, and the other member uses "Paste compare code". There is no QR: Desktop cannot decode
  one. Comparing with Bob gives one of: identical; you're behind (Bob has messages you don't; the
  app fetches them); Bob is behind (you hold everything his code points at); or "Bob has 1 message
  you don't (·k7f2). Asked; no answer." That last result is a fact about Bob and you, not a charge
  against the server.
- **A rejected banner.** **[amendment]** On restore or merge, if `open` fails: "This copy of the
  chat was altered: message ·9ac1 is missing", and the copy is not loaded. "Keep what
  verifies" loads the part that verifies, marked imported (theorem (4)). This catches a removed or
  changed message that a later message links. It does not catch a removed or changed newest
  message, or an extra one (§4, the limits).
- **Import, with a collapsed unconfirmed section.** **[amendment]** A history imported from a file
  starts as imported. Messages nobody has confirmed sit in a collapsed section, without avatars or
  live links, never inline under a member's name. As live messages arrive, they move out: "held by
  Alice" once a live message from Alice reaches them, normal once their author's does, "not
  confirmed by Bob" if Bob writes in parallel without reaching them (theorems (5) and (6);
  `RESTORE_PLAN.md`).
- **A disown alarm.** **[amendment]** If someone links a message in your name that you did not
  send, your app still accepts it (refusing would stall everything that builds on it), warns you
  "someone linked a message in your name you did not send", and lists it in `disown` in your next
  message. The other members' apps then mark it "not confirmed by" you.
- **Checkpoints and "confirmed by"** (optional, not in the demo). **[amendment]** A message whose
  text is "checkpoint" from someone who is caught up pins down the whole chat; its code can be read
  aloud. "Confirmed by" (formerly "seen by") is computed from live messages only: Bob has
  a message if a live message of his reaches it. The server cannot forge it, only withhold it.
  Links are receipts the whole group can see: they show which messages each member had when they
  wrote.
- **A fork marker** (optional, not in the demo). **[amendment]** Two live messages from the same
  author with the same timestamp but different digests are both shown and marked "sent as two
  versions" (a consequence of merge being union; §4). The app never silently drops the second one
  as a duplicate.
- **"zrdt unavailable".** **[amendment]** If `zrdtd` stops, a banner says so, and nothing is marked
  accepted until it is back. The app shows which backend runs, and its version.

**[amendment]** Words are for glancing. The compare code carries the full heads; a word list is
only an "equal?" fingerprint and has at least 12 words (128 bits), so that neither the server nor
a member can grind two different histories into the same words.

## 7. Overhead with n members

Almost nothing grows with the group size. The costs grow with how many people write at the same
time, which is usually one or two.

| | Cost | Depends on n? |
|---|---|---|
| Extra bytes per message **[amendment]** | 32 B per head the sender links, plus a 32 B salt and a few bytes of framing. Turn-taking: about 70 B. Burst of k concurrent writers: about 32·k + 40 B. | Only through k ≤ n; typical k = 1–2 |
| Work to receive a message **[amendment]** | Two SHA-256 in Lean (the commitment and the record), one lookup per link, and two round trips to `zrdtd` (`COMMIT`, then `ACCEPT`; about 55 µs each from an Electron preload, review §1.3): well under a millisecond for a text message. Re-running `CLASSIFY` afterwards grows with the history, not with n. | No |
| Storage per message **[amendment]** | About 150 B of structure (record plus digest; 32 B more per extra link). 100k messages ≈ 15 MB. Desktop also keeps the opening (salt plus message bytes), about the size of the message itself. | No |
| State to protect | The heads: 32 B each, at most one per member who wrote since everyone last caught up. | ≤ 32·n B; usually 32–64 B |
| Catching up | Swap heads, fetch only the missing messages, one negotiation round trip. | No |
| Full audit of a restore **[amendment]** | One pass over the history; SHA-256 in Lean takes about 9 µs per record. 100k messages: about a second (review §1.5). | No |
| Per-member bookkeeping | None. No acknowledgements, no per-member counters. | No |

Signal already sends a group message once per recipient; zrdt's bytes ride inside that body. For
comparison, vector clocks cost O(n) bytes on every message, always; MLS's proposed AppAck costs
O(n) acknowledgement messages per epoch. Hash links cost O(concurrency) instead. If a very large
group ever has a burst of hundreds of concurrent writers, links per message can be capped (say at
16); the remaining heads get linked by later messages, since linking an older head is allowed.

## 8. Integration plan (overview)

Details, protobuf changes, file paths and the demo script are in `APP.md`.

- **Signal-Desktop fork.** **[amendment]** Pinned to `v8.33.0`, built and run on the Mac mini. The
  sender's current heads and the salt go into a new sub-message of `DataMessage`,
  `optional ZrdtMeta zrdt = 200`, with the fields `links`, `nonce`, `version` and `disown`. It is a
  sub-message, not a bare list, because an empty list is invisible on the wire: a first message
  (no heads yet) would look like a stock one. Unmodified clients ignore the unknown field.
- **Scope.** **[amendment]** A record is a group (GroupV2) message from the normal send path, not a
  story, reaction or edit. Edits, deletes, reactions, polls, pins, timer, profile and group changes
  are not covered. 1:1 chats and Note-to-self are out. Membership changes after a group starts
  using zrdt are a non-goal; the demo group is fixed. Send and receive apply the same rule.
- **On send.** **[amendment]** Inside the send job, once: read the heads, pick a salt, build the
  message bytes, ask `zrdtd` to `COMMIT` and `ACCEPT`, save, and send those same bytes on every
  retry.
- **On receive**, **[amendment]** in `MessageReceiver`, after Signal has decrypted the message and
  checked membership, and before Desktop's local drops, the fork asks `zrdtd` to `ACCEPT` the
  record. Accepted messages are stored as today; records whose links do not resolve go to a
  pending table and produce a gap row. A record is live when Signal's envelope sender is the
  record's author. Records go into their own SQL tables, as structure only; Desktop keeps each
  message's content as an attribute it erases on delete, expiry and view-once.
- **Recovery by digest.** **[amendment]** Three new message types inside Signal's `Content`:
  `ZrdtResendRequest`, `ZrdtResend` and `ZrdtNotFound`. The request goes 1:1 to the member whose
  message referenced the digest, then to the group; replies are always 1:1. Anyone who holds the
  record may relay it with its content. The receiver hands both to `zrdtd` (`ACCEPT_RECORD`), which
  checks the content against the commitment before accepting the record **[amendment]**, and
  shows it as "relayed by X". That proves it is the record that
  was linked, not who wrote it. The app then asks the author 1:1, and the author's app sends the
  original again through Signal's own resend path (within 24 hours). That copy arrives live, so it
  is confirmed by its author at once. A relayed message never changes anything outside itself, for
  example the sender's profile key. A "not found" reply is not decisive: the server can drop the
  request or the reply, and an honest member may lack the record. Stock clients log the three new
  message types as unsupported and drop them; nothing is shown.
- **Whole-history restore** **[amendment]** from anyone. A dump is the store (structure) plus a
  content section keyed by digest. It leaves out the content of disappearing, deleted-for-everyone
  and view-once messages, and anyone who joined after a message was sent gets its structure only.
  Export asks for OS authentication and warns "do not share". Live messages then confirm it:
  `RESTORE_PLAN.md`. This holds against the server, and against a dump-giver who sends no live
  messages. A member who gives a dump and also links fakes in live messages is caught only by
  disown.
- **The villain.** **[amendment]** Signal-Desktop ships a mock Signal server for its own
  integration tests. An `EvilServer` subclass overrides how it hands out messages
  (`handleMessage` and `prepareMultiDeviceMessage`, not `send()`) with a few rules: drop one group
  message from one member to another, discard everything to one member (`blackhole`), and hold
  then release. It still cannot read the messages. Like a real server, it can tell who sent a group
  message from the set of recipients. Each rule is one attack in the demo. It also provisions the
  fake "phones" the four desktops (Alice, Bob, Carol, Dave) link to, so no phone numbers are needed
  and all four run on one machine. A TLS-terminating proxy in front of Signal's staging server is
  a stretch goal for a demo against the real network.
- **Demo**, **[amendment]** four desktops, five beats, under 4 minutes:
  1. Chat normally; compare codes match.
  2. The server drops Alice's message to Carol; Bob sends a plain reply. Carol sees a gap row; the
     message comes back "relayed by Bob", then "confirmed by Alice".
  3. The server discards everything to Carol; Alice sends and nobody replies. Carol pastes Bob's
     compare code: "Bob has 1 message you don't. Asked; no answer." Once the villain stops, "Ask
     again" recovers it.
  4. A doctored restore, with a linked message removed, is rejected and names the missing digest;
     "keep what verifies" loads the rest as imported.
  5. Dave imports Bob's export, with two fakes in Bob's name added on top. Everything starts
     collapsed and grey. Alice writes: the genuine history becomes "held by Alice". Bob writes: his
     genuine messages are confirmed, and the two fakes are marked "not confirmed by Bob".
- **Android** is a stretch goal. **[amendment]** It would need an Android build of `zrdtd`, or a
  JNI shim over the same Lean `handle` (`APP.md` §11).

## 9. What is not proved, and not claimed

- **Who wrote a message.** **[amendment]** `author` is a claim. Signal checks it only for a record
  that arrives live from its author. For a relayed or imported record, zrdt gives
  `authorConfirmed` (§4 (6)), and that theorem assumes the author's own app disowns what it did not
  send. Without disown, "Alice wrote it and the server dropped it" and "Mallory made it up" look the
  same (the fourth limit).
- **Confidentiality and privacy.** **[amendment]** zrdt hides nothing by itself; Signal's
  encryption does.
  - Live zrdt data (links, salt, disown list) rides inside Signal's encrypted messages.
  - The store holds structure, not text (§2). Each message's content (salt plus message bytes, the
    *opening*) is kept by Desktop as a message attribute that Desktop's delete, disappearing-message
    and view-once paths erase.
  - The structure itself stays: the authors, the causal shape and the count of messages that have
    expired or been deleted remain in every member's store.
  - Links are receipts the whole group can see: each message shows which messages its sender had,
    beyond what Signal's own delivery and read receipts show.
  - A restore dump leaves Signal's encryption. So export asks for OS authentication and warns "do
    not share", as Signal's own export does. It leaves out the content of disappearing,
    deleted-for-everyone and view-once messages, and the importer refuses such content. Anyone who
    joined after a message was sent gets its structure only. There is no "mirror" or "server"
    transport unless the dump is encrypted.
  - Signal's own link-and-sync and backups carry no zrdt data. A device restored that way has its
    full timeline and an empty store; matching the two up is out of scope.
- **Liveness.** A server can refuse to deliver anything. zrdt detects withholding only when
  something later references the withheld message, or when two members compare heads. It cannot
  make a server deliver. **[amendment]** And a gap or a "withheld" result shows that someone is
  inconsistent, not that the server is at fault: a member can link a made-up digest, and an
  offline author looks the same.
- **What `open` catches.** **[amendment]** A removed or changed record that another record links, a
  link to nothing, a changed chat id, malformed bytes. Not a removed or edited newest record, and
  not a made-up record added on top (§4 (4)).
- **Scope.** **[amendment]** Edits, deletes, reactions, polls, pins, timer, profile and group
  changes, 1:1 chats, and membership changes after a group starts using zrdt. Blocking a member
  makes the two stores differ for good, in both directions.
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
