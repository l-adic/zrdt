import Zrdt.Encode

/-!
# The commitment to a message's content (docs/PLAN.md §3.4)

A record does not carry the message. It carries a commitment to it:

    commit = SHA-256("zrdtP1" ‖ group (32) ‖ author (16) ‖ nonce (32) ‖ committed bytes)

The **committed bytes** are the Signal `DataMessage` wire bytes with every top-level field 15
(`groupV2`, which holds the group master key) and every top-level field 200 (`zrdt`, which holds
the record's links) removed. Every other field stays, byte for byte and in its original order:
the timestamp, the body, quotes, mentions, attachments, previews, stickers, and fields this code
does not know. Removing the fields again changes nothing, so the opening that the app stores and
relays (the nonce and the committed bytes) checks against the same commitment.

**The scan** reads only the top level of the message. A field is a key, then a value. The key is
a varint holding `field number * 8 + wire type`. The value depends on the wire type:

- 0: a varint;
- 1: 8 bytes;
- 2: a varint length, then that many bytes;
- 5: 4 bytes.

A varint is 1 to 10 bytes; each byte holds 7 bits, low bits first, and all but the last byte have
the top bit set. The scan rejects the input (`none`) if a field is cut short, a varint is longer
than 10 bytes, a key does not fit in 32 bits, a field number is 0, or a wire type is 3, 4, 6 or 7
(3 and 4 are protobuf's old "groups", which Signal's `DataMessage` does not use). The empty input
is a valid, empty message.

What the scan keeps is not proved against a protobuf parser: that part is small and in the
trusted base, and the examples below and the vectors (`Zrdt.Vectors`) pin what it does. What is
proved: removing the fields again changes nothing (`committedBytes_idem`), and the opening `COMMIT`
returns always matches its commitment (`commitWithOpening_matches`).
-/

namespace Zrdt

/-! ## Reading the top level of a protobuf message -/

/-- Read a varint from `b` starting at `pos`: its value and the position just after it. `none`
if the input ends first or the varint is longer than 10 bytes. -/
def readVarint (b : ByteArray) (pos : Nat) : Option (Nat × Nat) :=
  go pos 0 0 10
where
  /-- Continue at byte `i`. The bits read so far are `acc`; the next 7 bits go at `shift`. At most
  `left` more bytes may be read. -/
  go (i shift acc : Nat) : Nat → Option (Nat × Nat)
    | 0 => none
    | left + 1 =>
      if h : i < b.size then
        let byte := b[i]
        let acc := acc + ((byte &&& 0x7f).toNat <<< shift)
        if byte < 0x80 then some (acc, i + 1) else go (i + 1) (shift + 7) acc left
      else none

#guard readVarint ⟨#[0x05]⟩ 0 == some (5, 1)
#guard readVarint ⟨#[0x00, 0xac, 0x02]⟩ 1 == some (300, 3)   -- 300 = 0b10_0101100
#guard readVarint ⟨#[0x80, 0x00]⟩ 0 == some (0, 2)            -- a longer form of 0 is allowed
#guard readVarint ⟨#[0x80]⟩ 0 == none                         -- cut short
#guard readVarint ⟨Array.replicate 9 0xff ++ #[0x01]⟩ 0 == some (2^64 - 1, 10)
#guard readVarint ⟨Array.replicate 10 0xff ++ #[0x01]⟩ 0 == none -- 11 bytes

/-- One top-level field of a message: its number, and where its bytes (key and value) start and
stop in the input. -/
structure Field where
  /-- The field number. -/
  num : Nat
  /-- The position of the first byte of the key. -/
  start : Nat
  /-- The position just after the value. -/
  stop : Nat
deriving DecidableEq, Repr

/-- The field whose key starts at `pos`, or `none` if it is malformed (see the module header). -/
def readField (b : ByteArray) (pos : Nat) : Option Field := do
  let (key, p) ← readVarint b pos
  guard (key < 2^32 ∧ key >>> 3 ≠ 0)
  let stop ← match key &&& 7 with
    | 0 => (readVarint b p).map (·.2)
    | 1 => if p + 8 ≤ b.size then some (p + 8) else none
    | 2 => do
      let (len, q) ← readVarint b p
      if q + len ≤ b.size then some (q + len) else none
    | 5 => if p + 4 ≤ b.size then some (p + 4) else none
    | _ => none
  pure ⟨key >>> 3, pos, stop⟩

-- Field 1, wire type 2, 2 bytes: `0a 02 68 69`.
#guard readField ⟨#[0x0a, 0x02, 0x68, 0x69]⟩ 0 == some ⟨1, 0, 4⟩
-- Field 7, wire type 0, the varint 300.
#guard readField ⟨#[0x38, 0xac, 0x02]⟩ 0 == some ⟨7, 0, 3⟩
-- The length says 3 bytes, only 2 follow.
#guard readField ⟨#[0x0a, 0x03, 0x68, 0x69]⟩ 0 == none
-- Field number 0, and wire type 3 (a group), are rejected.
#guard readField ⟨#[0x02, 0x00]⟩ 0 == none
#guard readField ⟨#[0x0b]⟩ 0 == none
-- A key of 2^32 does not fit in 32 bits.
#guard readField ⟨#[0x80, 0x80, 0x80, 0x80, 0x10, 0x00]⟩ 0 == none

/-- All top-level fields of a message, in order. `none` if any field is malformed. -/
def fields (b : ByteArray) : Option (Array Field) :=
  go 0 #[] (b.size + 1)
where
  /-- Read the fields from `pos` on, after the ones in `acc`. Every field takes at least one
  byte, so `b.size + 1` rounds are always enough; running out returns `none`. -/
  go (pos : Nat) (acc : Array Field) : Nat → Option (Array Field)
    | 0 => none
    | fuel + 1 =>
      if pos < b.size then do
        let f ← readField b pos
        go f.stop (acc.push f) fuel
      else some acc

#guard fields ByteArray.empty == some #[]
#guard fields ⟨#[0x0a, 0x02, 0x68, 0x69, 0x38, 0x01]⟩ == some #[⟨1, 0, 4⟩, ⟨7, 4, 6⟩]
#guard fields ⟨#[0x0a, 0x02, 0x68, 0x69, 0x38]⟩ == none

/-- The message `b` with every top-level field whose number satisfies `drop` removed. The other
fields are kept byte for byte, in order. `none` if `b` is malformed. -/
def dropFields (drop : Nat → Bool) (b : ByteArray) : Option ByteArray :=
  (fields b).map fun fs =>
    fs.foldl (init := ByteArray.emptyWithCapacity b.size) fun out f =>
      if drop f.num then out else out ++ b.extract f.start f.stop

#guard dropFields (· == 1) ⟨#[0x0a, 0x02, 0x68, 0x69, 0x38, 0x01]⟩ == some ⟨#[0x38, 0x01]⟩

/-! ## The commitment -/

/-- The bytes the commitment covers: the `DataMessage` with every top-level field 15 (`groupV2`)
and 200 (`zrdt`) removed. `none` if the message is malformed. -/
def committedBytes (dataMessage : ByteArray) : Option ByteArray :=
  dropFields (fun n => n == 15 || n == 200) dataMessage

#guard committedBytes ByteArray.empty == some ByteArray.empty

/-- The 6-byte tag that starts every commitment input: `"zrdtP1"`. -/
def commitTag : ByteArray := "zrdtP1".toUTF8

example : commitTag.size = 6 := by decide

/-- The 32 random bytes a sender picks for each message (`ZrdtMeta.nonce`). -/
structure Nonce where
  /-- The 32 bytes. -/
  bytes : ByteArray
  /-- There are exactly 32 of them. -/
  size_eq : bytes.size = 32

/-- A nonce from a byte array, if it has exactly 32 bytes. -/
def Nonce.ofBytes? (b : ByteArray) : Option Nonce :=
  if h : b.size = 32 then some ⟨b, h⟩ else none

#guard (Nonce.ofBytes? ⟨Array.replicate 32 7⟩).isSome
#guard (Nonce.ofBytes? ⟨Array.replicate 31 7⟩).isNone

/-- The commitment of a message (layout in the module header). `none` if the `DataMessage` bytes
are malformed. -/
def commit (group : GroupId) (author : Aci) (nonce : Nonce) (dataMessage : ByteArray) :
    Option Digest :=
  (committedBytes dataMessage).map fun s =>
    sha256 (commitTag ++ group.bytes ++ author.bytes ++ nonce.bytes ++ s)

/-! ## The opening

The **opening** of a message is what the app stores and relays in place of the message:

    opening = nonce (32) ‖ committed bytes

`COMMIT` returns it next to the commitment. It never holds field 15 (the group master key) or
field 200. A record and an opening that a relay or an import brings are checked together by
`openingMatches`: the commitment of the opening, under the record's group and author, must be the
record's commit. -/

/-- The commitment and the opening of a message. `none` if the `DataMessage` is malformed. -/
def commitWithOpening (group : GroupId) (author : Aci) (nonce : Nonce) (dataMessage : ByteArray) :
    Option (Digest × ByteArray) :=
  (committedBytes dataMessage).map fun s =>
    (sha256 (commitTag ++ group.bytes ++ author.bytes ++ nonce.bytes ++ s), nonce.bytes ++ s)

/-- `commitWithOpening` gives the commitment `commit` gives. -/
theorem commitWithOpening_fst (group : GroupId) (author : Aci) (nonce : Nonce)
    (dataMessage : ByteArray) :
    (commitWithOpening group author nonce dataMessage).map (·.1) =
      commit group author nonce dataMessage := by
  simp only [commitWithOpening, commit, Option.map_map]
  rfl

/-- An opening split into its nonce and its committed bytes. `none` if it is shorter than 32
bytes. -/
def splitOpening (o : ByteArray) : Option (Nonce × ByteArray) := do
  let n ← Nonce.ofBytes? (o.extract 0 32)
  pure (n, o.extract 32 o.size)

/-- Whether `o` is an opening of a message with commitment `c`, by this author in this group: it
is a nonce and committed bytes (well-formed, with no field 15 or 200 left in them), and their
commitment is `c`. -/
def openingMatches (group : GroupId) (author : Aci) (c : Digest) (o : ByteArray) : Bool :=
  match splitOpening o with
  | none => false
  | some (n, m) => decide (committedBytes m = some m ∧ commit group author n m = some c)

/-- `splitOpening` cuts the opening in two: the nonce, then the rest. -/
theorem splitOpening_eq {o : ByteArray} {n : Nonce} {m : ByteArray}
    (h : splitOpening o = some (n, m)) : o = n.bytes ++ m := by
  simp only [splitOpening, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨n', hn, rfl, rfl⟩ := h
  unfold Nonce.ofBytes? at hn
  split at hn
  · rename_i hs
    cases hn
    have h32 : 32 ≤ o.size := by
      simp only [ByteArray.size_extract] at hs; omega
    show o = o.extract 0 32 ++ o.extract 32 o.size
    rw [← ByteArray.extract_eq_extract_append_extract 32 (Nat.zero_le _) h32,
      ByteArray.extract_zero_size]
  · cases hn

/-- **What a matching opening means.** If `openingMatches group author c o`, then `o` is a nonce
followed by message bytes that hold no field 15 or 200, and the commitment of that nonce and
those bytes, by `author` in `group`, is `c`. -/
theorem openingMatches_spec {group : GroupId} {author : Aci} {c : Digest} {o : ByteArray}
    (h : openingMatches group author c o = true) :
    ∃ (n : Nonce) (m : ByteArray), o = n.bytes ++ m ∧ committedBytes m = some m ∧
      commit group author n m = some c := by
  unfold openingMatches at h
  split at h
  · cases h
  · rename_i n m hs
    obtain ⟨h1, h2⟩ := of_decide_eq_true h
    exact ⟨n, m, splitOpening_eq hs, h1, h2⟩

/-! ## Removing the fields again changes nothing

`committedBytes_idem`: the committed bytes are a well-formed message with no field 15 or 200, so
removing those fields from them again gives them back. `commitWithOpening_matches`: so the opening
that `COMMIT` returns always passes `openingMatches`, under the same group and author. The proof
glues the kept fields back together (`chunks`), and shows that reading the glued bytes finds the
same fields, moved (`packed`): a field read only looks at its own bytes (`readField_shift`). -/

/-- A varint read ends after it starts, and inside the input. -/
theorem readVarint_go_bounds {b : ByteArray} : ∀ {left i shift acc v e : Nat},
    readVarint.go b i shift acc left = some (v, e) → i < e ∧ e ≤ b.size
  | 0, _, _, _, _, _, h => by simp [readVarint.go] at h
  | left + 1, i, shift, acc, v, e, h => by
    unfold readVarint.go at h
    split at h
    · rename_i hi
      dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        omega
      · have := readVarint_go_bounds h
        omega
    · simp at h

/-- A varint read only looks at its own bytes: the same bytes at another place, in another
input, read the same. -/
theorem readVarint_go_shift {b b' : ByteArray} : ∀ {left i i' shift acc v e : Nat},
    readVarint.go b i shift acc left = some (v, e) →
    (∀ k, i + k < e → b'[i' + k]? = b[i + k]?) →
    readVarint.go b' i' shift acc left = some (v, i' + (e - i))
  | 0, _, _, _, _, _, _, h, _ => by simp [readVarint.go] at h
  | left + 1, i, i', shift, acc, v, e, h, hb => by
    have ⟨hie, heb⟩ := readVarint_go_bounds h
    have h0 := hb 0 (by omega)
    simp only [Nat.add_zero] at h0
    unfold readVarint.go at h ⊢
    have hi : i < b.size := by omega
    simp only [hi, ↓reduceDIte] at h
    rw [getElem?_pos b i hi] at h0
    have hi' : i' < b'.size := by
      rcases Nat.lt_or_ge i' b'.size with hlt | hge
      · exact hlt
      · rw [getElem?_neg b' i' (by omega)] at h0; cases h0
    rw [getElem?_pos b' i' hi', Option.some.injEq] at h0
    simp only [hi', ↓reduceDIte, h0]
    split at h
    · rename_i hlt
      simp only [hlt, ↓reduceIte]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      omega
    · rename_i hlt
      simp only [hlt, ↓reduceIte]
      have := readVarint_go_shift (i' := i' + 1) h (fun k hk => by
        have := hb (k + 1) (by omega)
        rwa [show i' + (k + 1) = i' + 1 + k by omega, show i + (k + 1) = i + 1 + k by omega]
          at this)
      rw [this]
      have := readVarint_go_bounds h
      congr 2
      omega

/-- See `readVarint_go_bounds`. -/
theorem readVarint_bounds {b : ByteArray} {i v e : Nat} (h : readVarint b i = some (v, e)) :
    i < e ∧ e ≤ b.size := readVarint_go_bounds h

/-- See `readVarint_go_shift`. -/
theorem readVarint_shift {b b' : ByteArray} {i i' v e : Nat} (h : readVarint b i = some (v, e))
    (hb : ∀ k, i + k < e → b'[i' + k]? = b[i + k]?) :
    readVarint b' i' = some (v, i' + (e - i)) := readVarint_go_shift h hb

/-- A field read only looks at its own bytes: it ends after it starts and inside the input, and
the same bytes at another place, in another input with room for them, read as the same field
moved there. -/
theorem readField_shift {b b' : ByteArray} {pos pos' : Nat} {f : Field}
    (h : readField b pos = some f)
    (hb : ∀ k, pos + k < f.stop → b'[pos' + k]? = b[pos + k]?) :
    f.start = pos ∧ pos < f.stop ∧ f.stop ≤ b.size ∧
      (pos' + (f.stop - pos) ≤ b'.size →
        readField b' pos' = some ⟨f.num, pos', pos' + (f.stop - pos)⟩) := by
  have hsub : ∀ q, pos ≤ q → ∀ k, q + k < f.stop → b'[pos' + (q - pos) + k]? = b[q + k]? := by
    intro q hq k hk
    have := hb (q - pos + k) (by omega)
    rwa [show pos + (q - pos + k) = q + k by omega,
      show pos' + (q - pos + k) = pos' + (q - pos) + k by omega] at this
  unfold readField at h ⊢
  cases hk : readVarint b pos with
  | none => simp [hk] at h
  | some kp =>
    obtain ⟨key, p⟩ := kp
    have ⟨hpp, hpb⟩ := readVarint_bounds hk
    simp only [hk, Option.bind_eq_bind, Option.bind_some] at h
    by_cases hg : key < 2 ^ 32 ∧ key >>> 3 ≠ 0
    case neg => simp [guard, hg, failure] at h
    have hgt : (key < 2 ^ 32 ∧ key >>> 3 ≠ 0) = True := eq_true hg
    simp only [guard, hgt, ite_true, pure, Option.bind_some] at h
    have hk' : ∀ e, p ≤ e → pos + (e - pos) ≤ f.stop →
        readVarint b' pos' = some (key, pos' + (p - pos)) := fun e hpe hef =>
      readVarint_shift hk (fun k hk => by simpa using hsub pos (Nat.le_refl _) k (by omega))
    split at h
    · rename_i heq
      cases hv : readVarint b p with
      | none => simp [hv] at h
      | some w =>
        obtain ⟨v, e⟩ := w
        have ⟨hpe, heb⟩ := readVarint_bounds hv
        simp only [hv, Option.map_some, Option.bind_some, Option.some.injEq] at h
        subst h
        have hv' := readVarint_shift (b' := b') (i' := pos' + (p - pos)) hv
          (fun k hk => hsub p (by omega) k (by simp; omega))
        simp only [hk' e (by omega) (by simp; omega), hv', Option.bind_eq_bind, Option.bind_some,
          guard, hgt, ite_true, pure, Option.map_some, heq]
        refine ⟨trivial, by omega, heb, fun _ => ?_⟩
        congr 2
        omega
    · rename_i heq
      split at h
      · rename_i h8
        simp only [Option.some.injEq] at h
        subst h
        simp only [hk' (p + 8) (by omega) (by simp; omega), Option.bind_eq_bind, Option.bind_some,
          guard, hgt, ite_true, pure, heq]
        refine ⟨trivial, by omega, h8, fun hsz => ?_⟩
        split
        · congr 2; omega
        · rename_i hn; exact absurd (by omega) hn
      · simp at h
    · rename_i heq
      cases hv : readVarint b p with
      | none => simp [hv] at h
      | some w =>
        obtain ⟨len, q⟩ := w
        have ⟨hpq, hqb⟩ := readVarint_bounds hv
        simp only [hv, Option.bind_some] at h
        split at h
        · rename_i hql
          simp only [Option.some.injEq] at h
          subst h
          have hv' := readVarint_shift (b' := b') (i' := pos' + (p - pos)) hv
            (fun k hk => hsub p (by omega) k (by simp; omega))
          simp only [hk' (q + len) (by omega) (by simp; omega), hv', Option.bind_eq_bind,
            Option.bind_some, guard, hgt, ite_true, pure, heq]
          refine ⟨trivial, by omega, hql, fun hsz => ?_⟩
          split
          · congr 2; omega
          · rename_i hn; exact absurd (by omega) hn
        · simp at h
    · rename_i heq
      split at h
      · rename_i h4
        simp only [Option.some.injEq] at h
        subst h
        simp only [hk' (p + 4) (by omega) (by simp; omega), Option.bind_eq_bind, Option.bind_some,
          guard, hgt, ite_true, pure, heq]
        refine ⟨trivial, by omega, h4, fun hsz => ?_⟩
        split
        · congr 2; omega
        · rename_i hn; exact absurd (by omega) hn
      · simp at h
    · simp at h

/-- A field read from `b` at `pos` starts at `pos`, takes at least one byte, and ends inside `b`. -/
theorem readField_bounds {b : ByteArray} {pos : Nat} {f : Field} (h : readField b pos = some f) :
    f.start = pos ∧ pos < f.stop ∧ f.stop ≤ b.size :=
  let ⟨h1, h2, h3, _⟩ := readField_shift (b' := b) (pos' := pos) h (fun _ _ => rfl)
  ⟨h1, h2, h3⟩

/-- Every field that `fields.go` returns, past those in `acc`, is read at its own start. -/
theorem fields_go_mem {b : ByteArray} : ∀ {fuel pos acc fs}, fields.go b pos acc fuel = some fs →
    ∀ f ∈ fs, f ∈ acc ∨ readField b f.start = some f
  | 0, _, _, _, h => by simp [fields.go] at h
  | fuel + 1, pos, acc, fs, h => by
    unfold fields.go at h
    split at h
    · cases hf : readField b pos with
      | none => simp [hf] at h
      | some f =>
        simp only [hf, Option.bind_eq_bind, Option.bind_some] at h
        intro g hg
        rcases fields_go_mem h g hg with h1 | h1
        · rw [Array.mem_push] at h1
          rcases h1 with h1 | rfl
          · exact Or.inl h1
          · right; rw [(readField_bounds hf).1]; exact hf
        · exact Or.inr h1
    · simp only [Option.some.injEq] at h
      subst h
      exact fun f hf => Or.inl hf

/-! ### Gluing fields back together -/

/-- A byte of `P ++ X ++ Y` in the `X` part. -/
theorem getElem?_mid {P X Y : ByteArray} {k : Nat} (hk : k < X.size) :
    (P ++ X ++ Y)[P.size + k]? = X[k]? := by
  have h1 : P.size + k < (P ++ X ++ Y).size := by simp; omega
  rw [getElem?_pos (P ++ X ++ Y) _ h1, getElem?_pos X k hk, Option.some.injEq,
    ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_right (by omega)]
  simp

/-- A byte of `b.extract i j`, read in `b`. -/
theorem getElem?_extract' {b : ByteArray} {i j k : Nat} (hk : i + k < j) (hj : j ≤ b.size) :
    (b.extract i j)[k]? = b[i + k]? := by
  have h1 : k < (b.extract i j).size := by simp; omega
  rw [getElem?_pos (b.extract i j) k h1, getElem?_pos b (i + k) (by omega),
    ByteArray.getElem_extract]

/-- The bytes of the fields `fs` of `b`, one after the other. -/
def chunks (b : ByteArray) : List Field → ByteArray
  | [] => ByteArray.empty
  | f :: fs => b.extract f.start f.stop ++ chunks b fs

/-- The fields `fs`, moved so that the first starts at `pos` and each starts where the one before
stops. -/
def packed (pos : Nat) : List Field → List Field
  | [] => []
  | f :: fs => ⟨f.num, pos, pos + (f.stop - f.start)⟩ :: packed (pos + (f.stop - f.start)) fs

/-- A field read from `b` takes at least one byte, so the glued bytes are at least as many as the
fields. -/
theorem length_le_size_chunks {b : ByteArray} :
    ∀ {fs : List Field}, (∀ f ∈ fs, readField b f.start = some f) → fs.length ≤ (chunks b fs).size
  | [], _ => by simp
  | f :: fs, h => by
    have ⟨_, h1, h2⟩ := readField_bounds (h f (by simp))
    have := length_le_size_chunks (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [chunks, ByteArray.size_append, ByteArray.size_extract, List.length_cons]
    omega

/-- Reading the glued bytes gives back the glued fields, moved. -/
theorem fields_go_chunks {b s : ByteArray} :
    ∀ {R : List Field} {P : ByteArray} {acc : Array Field} {fuel : Nat},
      (∀ f ∈ R, readField b f.start = some f) → R.length < fuel → s = P ++ chunks b R →
      fields.go s P.size acc fuel = some (acc ++ (packed P.size R).toArray)
  | [], P, acc, fuel + 1, _, _, hs => by
    unfold fields.go
    subst hs
    simp [chunks, packed]
  | f :: R, P, acc, fuel + 1, hR, hfuel, hs => by
    have hf := hR f (by simp)
    have ⟨hst, hlt, hle⟩ := readField_bounds hf
    have hsz : (b.extract f.start f.stop).size = f.stop - f.start := by simp; omega
    have hs' : s = P ++ b.extract f.start f.stop ++ chunks b R := by
      rw [hs, chunks, ByteArray.append_assoc]
    have hread : readField s P.size = some ⟨f.num, P.size, P.size + (f.stop - f.start)⟩ := by
      have := (readField_shift (b' := s) (pos' := P.size) hf (fun k hk => by
        rw [hs', getElem?_mid (by omega), getElem?_extract' (by omega) hle])).2.2.2
      rw [hst] at this
      exact this (by rw [hs']; simp; omega)
    unfold fields.go
    have hpos : P.size < s.size := by rw [hs']; simp; omega
    simp only [hpos, ↓reduceIte, hread, Option.bind_eq_bind, Option.bind_some]
    have ih := fields_go_chunks (s := s) (P := P ++ b.extract f.start f.stop)
      (acc := acc.push ⟨f.num, P.size, P.size + (f.stop - f.start)⟩) (fuel := fuel)
      (fun g hg => hR g (List.mem_cons_of_mem _ hg)) (by simp at hfuel; omega) hs'
    rw [ByteArray.size_append, hsz] at ih
    rw [ih]
    simp [packed]

/-- Removing nothing from the glued bytes gives them back. -/
theorem foldl_packed {b s : ByteArray} {drop : Nat → Bool} :
    ∀ {R : List Field} {P out : ByteArray},
      (∀ f ∈ R, readField b f.start = some f ∧ drop f.num = false) → s = P ++ chunks b R →
      (packed P.size R).foldl
          (fun out f => if drop f.num then out else out ++ s.extract f.start f.stop) out =
        out ++ chunks b R
  | [], _, _, _, _ => by simp [packed, chunks]
  | f :: R, P, out, hR, hs => by
    have ⟨hf, hd⟩ := hR f (by simp)
    have ⟨_, hlt, hle⟩ := readField_bounds hf
    have hsz : (b.extract f.start f.stop).size = f.stop - f.start := by simp; omega
    have hs' : s = P ++ b.extract f.start f.stop ++ chunks b R := by
      rw [hs, chunks, ByteArray.append_assoc]
    have hex : s.extract P.size (P.size + (f.stop - f.start)) = b.extract f.start f.stop := by
      rw [hs', ByteArray.append_assoc, ByteArray.extract_append, Nat.sub_self,
        Nat.add_sub_cancel_left, ByteArray.extract_append_eq_left hsz.symm]
      rw [ByteArray.extract_eq_empty_iff.mpr (Nat.min_le_right _ _), ByteArray.empty_append]
    have ih := foldl_packed (P := P ++ b.extract f.start f.stop)
      (out := out ++ b.extract f.start f.stop) (fun g hg => hR g (List.mem_cons_of_mem _ hg)) hs'
    rw [ByteArray.size_append, hsz] at ih
    simp only [packed, List.foldl_cons, hd, Bool.false_eq_true, ↓reduceIte, hex]
    rw [ih, chunks, ByteArray.append_assoc]

/-- The fold in `dropFields` glues the bytes of the kept fields. -/
theorem foldl_keep {b : ByteArray} {drop : Nat → Bool} : ∀ (fs : List Field) (out : ByteArray),
    fs.foldl (fun out f => if drop f.num then out else out ++ b.extract f.start f.stop) out =
      out ++ chunks b (fs.filter fun f => !drop f.num)
  | [], out => by simp [chunks]
  | f :: fs, out => by
    simp only [List.foldl_cons]
    rw [foldl_keep fs]
    by_cases hd : drop f.num
    · simp [hd]
    · simp [hd, chunks, ByteArray.append_assoc]

/-- **Removing fields twice changes nothing.** If `dropFields drop b` is `s`, then `s` is
well-formed, and removing the same fields from it again gives `s`. -/
theorem dropFields_idem {drop : Nat → Bool} {b s : ByteArray} (h : dropFields drop b = some s) :
    dropFields drop s = some s := by
  unfold dropFields at h
  cases hf : fields b with
  | none => simp [hf] at h
  | some fs =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    rw [← Array.foldl_toList, foldl_keep] at h
    have he : ByteArray.emptyWithCapacity b.size = ByteArray.empty := rfl
    rw [he, ByteArray.empty_append] at h
    generalize hKdef : fs.toList.filter (fun f => !drop f.num) = K at h
    have hK : ∀ f ∈ K, readField b f.start = some f ∧ drop f.num = false := by
      intro f hfK
      rw [← hKdef, List.mem_filter] at hfK
      obtain ⟨hmem, hd⟩ := hfK
      refine ⟨?_, by simpa using hd⟩
      rcases fields_go_mem hf f (by simpa using hmem) with h1 | h1
      · simp at h1
      · exact h1
    have hlen := length_le_size_chunks (fun f hf => (hK f hf).1)
    have hfs : fields s = some (#[] ++ (packed 0 K).toArray) := by
      have := fields_go_chunks (s := s) (P := ByteArray.empty) (acc := #[]) (fuel := s.size + 1)
        (fun f hf => (hK f hf).1) (by rw [← h]; omega) (by rw [← h, ByteArray.empty_append])
      unfold fields; simpa using this
    unfold dropFields
    rw [hfs]
    have hfold := foldl_packed (s := s) (drop := drop) (P := ByteArray.empty)
      (out := ByteArray.empty) hK (by rw [← h, ByteArray.empty_append])
    simp only [ByteArray.size_empty, ByteArray.empty_append] at hfold
    simp only [Option.map_some, Option.some.injEq, Array.empty_append, List.foldl_toArray']
    have he' : ByteArray.emptyWithCapacity s.size = ByteArray.empty := rfl
    rw [he', hfold, h]

/-- **The committed bytes are already committed bytes.** Removing fields 15 and 200 again changes
nothing. -/
theorem committedBytes_idem {b s : ByteArray} (h : committedBytes b = some s) :
    committedBytes s = some s :=
  dropFields_idem h

/-- An opening made of a nonce and bytes splits back into them. -/
theorem splitOpening_append (n : Nonce) (m : ByteArray) :
    splitOpening (n.bytes ++ m) = some (n, m) := by
  obtain ⟨nb, hn⟩ := n
  have h1 : (nb ++ m).extract 0 32 = nb := ByteArray.extract_append_eq_left hn.symm
  have h2 : (nb ++ m).extract 32 (nb ++ m).size = m :=
    ByteArray.extract_append_eq_right hn.symm (by simp [hn])
  simp only [splitOpening, h1, h2, Nonce.ofBytes?, hn, Option.bind_eq_bind, Option.pure_def]
  rfl

/-- **`COMMIT`'s opening matches its commitment.** The opening that `commitWithOpening` returns
next to commitment `c` passes `openingMatches` for the same group and author: it holds no field 15
or 200, and its commitment is `c`. -/
theorem commitWithOpening_matches {group : GroupId} {author : Aci} {nonce : Nonce}
    {dataMessage : ByteArray} {c : Digest} {o : ByteArray}
    (h : commitWithOpening group author nonce dataMessage = some (c, o)) :
    openingMatches group author c o = true := by
  unfold commitWithOpening at h
  cases hs : committedBytes dataMessage with
  | none => simp [hs] at h
  | some s =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hidem := committedBytes_idem hs
    unfold openingMatches
    rw [splitOpening_append]
    simp [hidem, commit]

/-! ## Examples -/

namespace Examples

/-- A nonce of 32 bytes `0x4e`. -/
def nonce : Nonce := ⟨⟨Array.replicate 32 0x4e⟩, rfl⟩

/-- Bytes from a list of numbers. -/
def bytesOf (xs : List Nat) : ByteArray := ⟨xs.toArray.map (·.toUInt8)⟩

/-- Field 1 (`body`): the text "hello". -/
def bodyField : ByteArray := bytesOf [0x0a, 5] ++ "hello".toUTF8

/-- Field 15 (`groupV2`): a `GroupContextV2` whose field 1 is a 32-byte master key `0x4b…`. -/
def groupV2Field : ByteArray := bytesOf [0x7a, 34, 0x0a, 32] ++ ⟨Array.replicate 32 0x4b⟩

/-- Field 7 (`timestamp`): the varint 1730419200000 (2024-11-01 00:00 UTC, in milliseconds). -/
def timestampField : ByteArray := bytesOf [0x38, 0x80, 0xa0, 0x96, 0xa8, 0xae, 0x32]

/-- Field 200 (`zrdt`): a `ZrdtMeta` whose field 1 holds one 32-byte link `0x11…`. The key 1602
is the varint `c2 0c`. -/
def zrdtField : ByteArray := bytesOf [0xc2, 0x0c, 34, 0x0a, 32] ++ ⟨Array.replicate 32 0x11⟩

/-- Field 99 with wire type 5 (4 bytes), a field this code does not know. The key 797 is the
varint `9d 06`. -/
def unknownField : ByteArray := bytesOf [0x9d, 0x06, 1, 2, 3, 4]

/-- A message with all five fields. -/
def dataMessage : ByteArray :=
  bodyField ++ groupV2Field ++ timestampField ++ zrdtField ++ unknownField

end Examples

open Examples

-- The timestamp varint is right.
#guard readVarint timestampField 1 == some (1730419200000, 7)
-- Fields 15 and 200 go; the others stay, in order.
#guard committedBytes dataMessage == some (bodyField ++ timestampField ++ unknownField)
-- Removing them again changes nothing.
#guard (committedBytes dataMessage).bind committedBytes == committedBytes dataMessage
-- A message without fields 15 and 200 is kept as it is.
#guard committedBytes (bodyField ++ timestampField) == some (bodyField ++ timestampField)
-- Every copy of field 15 goes, wherever it is, also with a longer form of its key (`fa 00`).
#guard committedBytes (groupV2Field ++ bodyField ++ groupV2Field) == some bodyField
#guard committedBytes (bytesOf [0xfa, 0x00, 0] ++ bodyField) == some bodyField
-- Malformed messages are rejected: cut short, or a field of wire type 3.
#guard committedBytes (dataMessage.extract 0 (dataMessage.size - 1)) == none
#guard committedBytes (bodyField ++ bytesOf [0x0b]) == none

-- The commitment. Expected value from Python's `hashlib`:
-- sha256(b"zrdtP1" + b"\x67"*32 + b"\xa1"*16 + b"\x4e"*32 + body + timestamp + unknown).
#guard (commit group alice nonce dataMessage).map Digest.toHex ==
  some "7b4974b33ab700cfc212dd43b4e58c23516eb12232c9275e0f7924b30eede3c6"
-- The same message without fields 15 and 200 has the same commitment; the opening checks.
#guard commit group alice nonce (bodyField ++ timestampField ++ unknownField) ==
  commit group alice nonce dataMessage
-- Another group, author or nonce gives another commitment.
#guard commit otherGroup alice nonce dataMessage != commit group alice nonce dataMessage
#guard commit group alice ⟨⟨Array.replicate 32 0⟩, rfl⟩ dataMessage !=
  commit group alice nonce dataMessage
#guard commit group alice nonce (bytesOf [0x0b]) == none

-- The opening: the nonce, then the message without fields 15 and 200.
#guard (commitWithOpening group alice nonce dataMessage).map (·.2) ==
  some (nonce.bytes ++ bodyField ++ timestampField ++ unknownField)
#guard (commitWithOpening group alice nonce dataMessage).map (·.1) ==
  commit group alice nonce dataMessage
-- It matches the commitment, under the same group and author only.
#guard match commitWithOpening group alice nonce dataMessage with
  | some (c, o) => openingMatches group alice c o && !openingMatches group Aci.zero c o &&
      !openingMatches otherGroup alice c o && !openingMatches group alice (dig 1) o
  | none => false
-- An opening that still holds field 15 (the master key) is refused, though its commitment is
-- the same; so are an opening cut inside its nonce and a malformed one.
#guard match commit group alice nonce dataMessage with
  | some c => !openingMatches group alice c (nonce.bytes ++ dataMessage) &&
      !openingMatches group alice c (nonce.bytes.extract 0 31) &&
      !openingMatches group alice c (nonce.bytes ++ bodyField ++ bytesOf [0x0b])
  | none => false

end Zrdt
