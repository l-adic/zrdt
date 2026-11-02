import Zrdt.Proto

/-!
# The apps' wire: protobuf writing, and what reading it back gives (docs/apps/BUILD_M1.md §B.2)

**Owner: lane base.** The protobuf writers the apps' committed messages are made of (`varint`,
`lenField`, `varintField`) and `u64be`, with the lemmas that read them back:

- `readVarint_varint`: `readVarint` (`Zrdt.Commit`) reads a `varint` back, up to 2^70;
- `fields_writeItems`, `fieldValue_len`, `dropFields_writeItems`: a message written as a list of
  fields (`Item`) is read back by `fields` field for field, a length-delimited field's value by
  `fieldValue`, and dropping fields it does not hold changes nothing (so `committedBytes` keeps it
  whole);
- the parser lemmas (`Parser.go_*`): what each `Proto.Parser` primitive reads, forward (from the
  bytes a writer wrote) and back (the bytes it read are the writer's bytes of what it returned).

Everything is Init and Std only. The torrent and git lanes may use these lemmas for their own
encodings; they never edit this file (BUILD_M1 §D).
-/

namespace Zrdt.AppBase

/-! ## Protobuf writing -/

/-- The protobuf varint of `n`, at most `fuel` bytes: seven bits per byte, low bits first. -/
def varintBytes : Nat → Nat → List UInt8
  | _, 0 => []
  | n, fuel + 1 =>
    if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: varintBytes (n / 128) fuel

/-- The protobuf varint of `n` (every number written here is below 2^64; at most 10 bytes). -/
def varint (n : Nat) : ByteArray := (varintBytes n 10).toByteArray

#guard varint 0 == ⟨#[0]⟩ && varint 300 == ⟨#[0xAC, 0x02]⟩
-- The key of field 201, wire type 2 (as `Commit.Examples.zrdtField` writes field 200's).
#guard varint (201 * 8 + 2) == ⟨#[0xCA, 0x0C]⟩

/-- A length-delimited field (wire type 2). -/
def lenField (num : Nat) (v : ByteArray) : ByteArray := varint (num * 8 + 2) ++ varint v.size ++ v

/-- A varint field (wire type 0). -/
def varintField (num : Nat) (v : Nat) : ByteArray := varint (num * 8) ++ varint v

/-- A 64-bit big-endian number (`u64`, BUILD_M1 §B.1). -/
def u64be (n : Nat) : ByteArray := u32be (n / 2 ^ 32) ++ u32be n

#guard u64be (2 ^ 32 + 7) == ⟨#[0, 0, 0, 1, 0, 0, 0, 7]⟩

namespace Wire

/-! ## Bytes at a position -/

/-- `x` sits in `b` at `pos`: every byte of `x` is the byte of `b` there. -/
def At (b : ByteArray) (pos : Nat) (x : ByteArray) : Prop :=
  ∀ k, k < x.size → b[pos + k]? = x[k]?

/-- A byte of `x ++ y`. -/
theorem getElem?_append (x y : ByteArray) (k : Nat) :
    (x ++ y)[k]? = if k < x.size then x[k]? else y[k - x.size]? := by
  split
  · rename_i hk
    rw [getElem?_pos (x ++ y) k (by simp [ByteArray.size_append]; omega), getElem?_pos x k hk,
      ByteArray.getElem_append_left hk]
  · rename_i hk
    by_cases hy : k - x.size < y.size
    · rw [getElem?_pos (x ++ y) k (by simp [ByteArray.size_append]; omega), getElem?_pos y _ hy,
        ByteArray.getElem_append_right (by omega)]
    · rw [getElem?_neg (x ++ y) k (by simp [ByteArray.size_append]; omega), getElem?_neg y _ hy]

theorem At.append_iff {b : ByteArray} {pos : Nat} {x y : ByteArray} :
    At b pos (x ++ y) ↔ At b pos x ∧ At b (pos + x.size) y := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp [ByteArray.size_append]; omega)
      rwa [getElem?_append, ite_eq_left hk] at this
    · have := h (x.size + k) (by simp [ByteArray.size_append]; omega)
      rw [getElem?_append, ite_eq_right (by omega), Nat.add_sub_cancel_left] at this
      rwa [Nat.add_assoc]
  · rintro ⟨h₁, h₂⟩ k hk
    rw [getElem?_append]
    split
    · exact h₁ k (by assumption)
    · have := h₂ (k - x.size) (by simp [ByteArray.size_append] at hk; omega)
      rwa [show pos + x.size + (k - x.size) = pos + k by omega] at this

theorem At.left {b : ByteArray} {pos : Nat} {x y : ByteArray} (h : At b pos (x ++ y)) :
    At b pos x := (At.append_iff.1 h).1

theorem At.right {b : ByteArray} {pos : Nat} {x y : ByteArray} (h : At b pos (x ++ y)) :
    At b (pos + x.size) y := (At.append_iff.1 h).2

/-- A byte array sits in itself at 0. -/
theorem At.self (x : ByteArray) : At x 0 x := fun k _ => by rw [Nat.zero_add]

/-- `x` sits in `P ++ x ++ S` after `P`. -/
theorem At.mid (P x S : ByteArray) : At (P ++ x ++ S) P.size x := by
  have := At.right (At.left (At.self (P ++ x ++ S)))
  rwa [Nat.zero_add] at this

/-- A non-empty `x` that sits in `b` at `pos` ends inside `b`. -/
theorem At.le_size {b : ByteArray} {pos : Nat} {x : ByteArray} (h : At b pos x)
    (hx : 0 < x.size) : pos + x.size ≤ b.size := by
  have := h (x.size - 1) (by omega)
  rw [getElem?_pos x _ (by omega)] at this
  by_cases hb : pos + (x.size - 1) < b.size
  · omega
  · rw [getElem?_neg b _ hb] at this; cases this

/-- The bytes of `b` where `x` sits are `x`. -/
theorem At.extract {b : ByteArray} {pos : Nat} {x : ByteArray} (h : At b pos x)
    (hle : pos + x.size ≤ b.size) : b.extract pos (pos + x.size) = x := by
  apply ByteArray.ext_getElem (by simp [ByteArray.size_extract]; omega)
  intro i hi hi'
  have := h i hi'
  rw [getElem?_pos b _ (by omega), getElem?_pos x i hi', Option.some.injEq] at this
  rw [ByteArray.getElem_extract, this]

/-- The bytes of `b` from `pos` to `q` sit in `b` at `pos`. -/
theorem At.of_extract {b : ByteArray} {pos q : Nat} (hq : q ≤ b.size) :
    At b pos (b.extract pos q) := by
  intro k hk
  simp only [ByteArray.size_extract] at hk
  rw [getElem?_pos (b.extract pos q) k (by simp [ByteArray.size_extract]; omega),
    getElem?_pos b _ (by omega), ByteArray.getElem_extract]

/-! ## Varints -/

theorem byte_lo {n : Nat} (h : n < 128) : n.toUInt8 < 0x80 ∧ (n.toUInt8 &&& 0x7f).toNat = n := by
  constructor
  · rw [UInt8.lt_iff_toNat_lt]; simp; omega
  · rw [UInt8.toNat_and]; simp
    rw [show (127 : Nat) = 2 ^ 7 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem byte_hi (n : Nat) : ¬ (n % 128 + 128).toUInt8 < 0x80 ∧
    ((n % 128 + 128).toUInt8 &&& 0x7f).toNat = n % 128 := by
  constructor
  · rw [UInt8.lt_iff_toNat_lt]; simp; omega
  · rw [UInt8.toNat_and]; simp
    rw [show (127 : Nat) = 2 ^ 7 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

/-- Reading `k + 1` bytes of a varint written in at most `k + 1` bytes gives its value, or
`none` when the value needs more bytes (every byte written then has its high bit set). -/
theorem readVarint_go_varintBytes (b : ByteArray) : ∀ (k n i shift acc : Nat),
    (∀ j (hj : j < (varintBytes n (k + 1)).length), b[i + j]? = some (varintBytes n (k + 1))[j]) →
    readVarint.go b i shift acc (k + 1) =
      if n < 128 ^ (k + 1) then some (acc + n * 2 ^ shift, i + (varintBytes n (k + 1)).length)
      else none
  | k, n, i, shift, acc, hb => by
    have h0 := hb 0 (by unfold varintBytes; split <;> simp)
    simp only [Nat.add_zero] at h0
    have hi : i < b.size := by
      rcases Nat.lt_or_ge i b.size with h | h
      · exact h
      · rw [getElem?_neg b i (by omega)] at h0; cases h0
    rw [getElem?_pos b i hi, Option.some.injEq] at h0
    unfold readVarint.go
    simp only [hi, ↓reduceDIte, h0]
    by_cases hn : n < 128
    · have hv : varintBytes n (k + 1) = [n.toUInt8] := by simp [varintBytes, hn]
      simp only [hv, List.getElem_cons_zero, (byte_lo hn).1, ↓reduceIte, (byte_lo hn).2,
        Nat.shiftLeft_eq, List.length_cons, List.length_nil]
      have : n < 128 ^ (k + 1) := Nat.lt_of_lt_of_le hn (Nat.le_self_pow (by omega) _)
      simp [this]
    · have hv : varintBytes n (k + 1) = (n % 128 + 128).toUInt8 :: varintBytes (n / 128) k := by
        simp [varintBytes, hn]
      simp only [hv, List.getElem_cons_zero, (byte_hi n).1, ↓reduceIte, (byte_hi n).2,
        Nat.shiftLeft_eq, List.length_cons]
      cases k with
      | zero =>
        simp [readVarint.go]; omega
      | succ k =>
        rw [readVarint_go_varintBytes b k (n / 128) (i + 1) (shift + 7) _ (fun j hj => by
          have := hb (j + 1) (by rw [hv]; simp; omega)
          simp only [hv, List.getElem_cons_succ] at this
          rwa [show i + (j + 1) = i + 1 + j by omega] at this)]
        have hiff : n / 128 < 128 ^ (k + 1) ↔ n < 128 ^ (k + 1 + 1) := by
          rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]
        by_cases hlt : n / 128 < 128 ^ (k + 1)
        · simp only [hlt, ↓reduceIte, hiff.1 hlt, Option.some.injEq, Prod.mk.injEq]
          refine ⟨?_, by omega⟩
          have hn' : n = n % 128 + 128 * (n / 128) := (Nat.mod_add_div n 128).symm
          rw [Nat.pow_add]
          conv => rhs; rw [hn']
          rw [Nat.add_mul, show (2 : Nat) ^ 7 = 128 from rfl]
          ac_rfl
        · have : ¬ n < 128 ^ (k + 1 + 1) := fun h => hlt (hiff.2 h)
          simp [hlt, this]

theorem size_varint (n : Nat) : (varint n).size = (varintBytes n 10).length := by
  simp [varint]

theorem length_varintBytes_pos (n k : Nat) : 0 < (varintBytes n (k + 1)).length := by
  unfold varintBytes; split <;> simp

theorem length_varintBytes_le : ∀ (n k : Nat), (varintBytes n k).length ≤ k
  | _, 0 => by simp [varintBytes]
  | n, k + 1 => by
    unfold varintBytes
    split
    · simp
    · have := length_varintBytes_le (n / 128) k
      simp; omega

theorem size_varint_pos (n : Nat) : 0 < (varint n).size := by
  rw [size_varint]; exact length_varintBytes_pos n 9

theorem size_varint_le (n : Nat) : (varint n).size ≤ 10 := by
  rw [size_varint]; exact length_varintBytes_le n 10

/-- **A varint reads back.** `readVarint` of the bytes `varint n` wrote gives `n` and the position
after them, for every `n` below 2^70 (ten bytes); above, it gives `none`. -/
theorem readVarint_varint {b : ByteArray} {i n : Nat} (h : At b i (varint n)) :
    readVarint b i = if n < 2 ^ 70 then some (n, i + (varint n).size) else none := by
  unfold readVarint
  have := readVarint_go_varintBytes b 9 n i 0 0 (fun j hj => by
    have hj' : j < (varint n).size := by simpa [varint] using hj
    rw [h j hj', getElem?_pos _ j hj']
    simp [varint, List.getElem_toByteArray])
  rw [this, show (128 : Nat) ^ (9 + 1) = 2 ^ 70 from rfl, size_varint]
  simp

theorem readVarint_varint_lt {b : ByteArray} {i n : Nat} (h : At b i (varint n)) (hn : n < 2 ^ 70) :
    readVarint b i = some (n, i + (varint n).size) := by
  rw [readVarint_varint h, ite_eq_left hn]

/-! ## Messages as lists of fields -/

/-- One top-level field as written: length-delimited (wire type 2) or a varint (wire type 0). -/
inductive Item
  | len (num : Nat) (v : ByteArray)
  | vint (num : Nat) (v : Nat)

/-- The field number. -/
def Item.num : Item → Nat
  | .len n _ => n
  | .vint n _ => n

/-- The field's bytes. -/
def Item.write : Item → ByteArray
  | .len n v => lenField n v
  | .vint n v => varintField n v

/-- The field reads back: its number is 1 to 2^29 - 1 (so its key fits 32 bits), its length or
value is below 2^70. -/
def Item.ok : Item → Prop
  | .len n v => 0 < n ∧ n < 2 ^ 29 ∧ v.size < 2 ^ 70
  | .vint n v => 0 < n ∧ n < 2 ^ 29 ∧ v < 2 ^ 70

/-- The fields one after another. -/
def writeItems : List Item → ByteArray
  | [] => .empty
  | it :: l => it.write ++ writeItems l

/-- Where `fields` finds the fields of `writeItems l` written from `pos` on. -/
def layout : Nat → List Item → List Field
  | _, [] => []
  | pos, it :: l => ⟨it.num, pos, pos + it.write.size⟩ :: layout (pos + it.write.size) l

theorem size_write_pos (it : Item) : 0 < it.write.size := by
  cases it with
  | len n v =>
    have := size_varint_pos (n * 8 + 2)
    simp only [Item.write, lenField, ByteArray.size_append]; omega
  | vint n v =>
    have := size_varint_pos (n * 8)
    simp only [Item.write, varintField, ByteArray.size_append]; omega

theorem map_num_layout : ∀ (pos : Nat) (l : List Item), (layout pos l).map (·.num) = l.map (·.num)
  | _, [] => rfl
  | pos, it :: l => by simp [layout, map_num_layout]

theorem key_shift (n w : Nat) (hw : w < 8) : (n * 8 + w) >>> 3 = n := by
  rw [Nat.shiftRight_eq_div_pow]; omega

theorem key_and (n w : Nat) (hw : w < 8) : (n * 8 + w) &&& 7 = w := by
  rw [show (7 : Nat) = 2 ^ 3 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

/-- `guard` of a true condition. -/
theorem guard_true {p : Prop} [Decidable p] (h : p) : (guard p : Option Unit) = some () := by
  simp [guard, h]

/-- **A written field reads back** as that field, at that place. -/
theorem readField_item {b : ByteArray} {pos : Nat} {it : Item} (h : At b pos it.write)
    (ho : it.ok) : readField b pos = some ⟨it.num, pos, pos + it.write.size⟩ := by
  have hend := At.le_size h (size_write_pos it)
  cases it with
  | len n v =>
    obtain ⟨hn0, hn, hv⟩ := ho
    simp only [Item.write, lenField, ByteArray.size_append] at h hend
    have hk := At.left (At.left h)
    have hl := At.right (At.left h)
    have hg : n * 8 + 2 < 2 ^ 32 ∧ (n * 8 + 2) >>> 3 ≠ 0 := by
      rw [key_shift n 2 (by omega)]; omega
    unfold readField
    rw [readVarint_varint_lt hk (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [guard_true hg]
    simp only [Option.bind_some, key_and n 2 (by omega)]
    rw [readVarint_varint_lt hl hv]
    simp only [Option.bind_some]
    rw [ite_eq_left (by omega)]
    simp only [pure, key_shift n 2 (by omega), Item.num, Item.write, lenField,
      ByteArray.size_append, Nat.add_assoc]
  | vint n v =>
    obtain ⟨hn0, hn, hv⟩ := ho
    simp only [Item.write, varintField, ByteArray.size_append] at h hend
    have hk := At.left h
    have hl := At.right h
    have hand := key_and n 0 (by omega)
    have hsh := key_shift n 0 (by omega)
    simp only [Nat.add_zero] at hand hsh
    have hg : n * 8 < 2 ^ 32 ∧ (n * 8) >>> 3 ≠ 0 := by rw [hsh]; omega
    unfold readField
    rw [readVarint_varint_lt hk (by omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [guard_true hg]
    simp only [Option.bind_some, hand]
    rw [readVarint_varint_lt hl hv]
    simp only [Option.map_some, Option.bind_some, pure, hsh, Item.num, Item.write, varintField,
      ByteArray.size_append, Nat.add_assoc]

/-- **`fields` reads the fields of a written message back**, from `pos` to the end. -/
theorem fields_go_items {b : ByteArray} : ∀ (l : List Item) (pos : Nat) (acc : Array Field)
    (fuel : Nat), (∀ it ∈ l, it.ok) → At b pos (writeItems l) →
    pos + (writeItems l).size = b.size → l.length < fuel →
    fields.go b pos acc fuel = some (acc ++ (layout pos l).toArray)
  | [], pos, acc, fuel + 1, _, _, hs, _ => by
    unfold fields.go
    simp only [writeItems, ByteArray.size_empty, Nat.add_zero] at hs
    simp [hs, layout]
  | it :: l, pos, acc, fuel + 1, ho, h, hs, hf => by
    simp only [writeItems] at h hs
    rw [ByteArray.size_append] at hs
    have h1 := At.left h
    have h2 := At.right h
    have hp := size_write_pos it
    unfold fields.go
    rw [ite_eq_left (by omega), readField_item h1 (ho it (by simp))]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [fields_go_items l (pos + it.write.size) _ fuel (fun x hx => ho x (by simp [hx])) h2
      (by omega) (by simp at hf; omega)]
    simp [layout]

theorem length_le_size_writeItems : ∀ l : List Item, l.length ≤ (writeItems l).size
  | [] => by simp [writeItems]
  | it :: l => by
    have := length_le_size_writeItems l
    have := size_write_pos it
    simp [writeItems, ByteArray.size_append]; omega

/-- **A written message reads back field for field.** -/
theorem fields_writeItems {l : List Item} (ho : ∀ it ∈ l, it.ok) :
    fields (writeItems l) = some (layout 0 l).toArray := by
  unfold fields
  rw [fields_go_items l 0 #[] _ ho (At.self _) (by omega)
    (by have := length_le_size_writeItems l; omega)]
  simp

/-- **A length-delimited field's value reads back.** -/
theorem fieldValue_len {b : ByteArray} {pos stop n : Nat} {v : ByteArray}
    (h : At b pos (lenField n v)) (ho : (Item.len n v).ok) :
    Serve.fieldValue b ⟨n, pos, stop⟩ = some v := by
  obtain ⟨hn0, hn, hv⟩ := ho
  have hend := At.le_size h (size_write_pos (.len n v))
  simp only [lenField, ByteArray.size_append] at h hend
  have hk := At.left (At.left h)
  have hl := At.right (At.left h)
  have hx := At.right h
  unfold Serve.fieldValue
  rw [readVarint_varint_lt hk (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [guard_true (key_and n 2 (by omega))]
  simp only [Option.bind_some]
  rw [readVarint_varint_lt hl hv]
  simp only [Option.bind_some]
  rw [guard_true (by omega)]
  simp only [Option.bind_some, pure, Option.some.injEq]
  rw [ByteArray.size_append, ← Nat.add_assoc] at hx
  exact hx.extract (by omega)

/-- Dropping fields keeps the bytes of the fields it keeps. -/
theorem foldl_layout {b : ByteArray} {drop : Nat → Bool} : ∀ (l : List Item) (pos : Nat)
    (out : ByteArray), (∀ it ∈ l, drop it.num = false) → At b pos (writeItems l) →
    pos + (writeItems l).size ≤ b.size →
    (layout pos l).foldl (fun out f => if drop f.num then out else out ++ b.extract f.start f.stop)
      out = out ++ writeItems l
  | [], _, out, _, _, _ => by simp [layout, writeItems, ByteArray.append_empty]
  | it :: l, pos, out, hd, h, hs => by
    simp only [writeItems, ByteArray.size_append] at h hs
    simp only [layout, List.foldl_cons, hd it (by simp), Bool.false_eq_true, ↓reduceIte]
    rw [(At.left h).extract (by omega)]
    rw [foldl_layout l _ _ (fun x hx => hd x (by simp [hx])) (At.right h) (by omega)]
    simp [writeItems, ByteArray.append_assoc]

/-- **Dropping fields a written message does not hold changes nothing.** -/
theorem dropFields_writeItems {l : List Item} {drop : Nat → Bool} (ho : ∀ it ∈ l, it.ok)
    (hd : ∀ it ∈ l, drop it.num = false) :
    dropFields drop (writeItems l) = some (writeItems l) := by
  unfold dropFields
  rw [fields_writeItems ho]
  simp only [Option.map_some, Option.some.injEq, List.foldl_toArray']
  have he : ByteArray.emptyWithCapacity (writeItems l).size = ByteArray.empty := rfl
  rw [he, foldl_layout l 0 _ hd (At.self _) (by omega), ByteArray.empty_append]

/-- `committedBytes` keeps a written message whole when it holds no field 15 or 200. -/
theorem committedBytes_writeItems {l : List Item} (ho : ∀ it ∈ l, it.ok)
    (hd : ∀ it ∈ l, it.num ≠ 15 ∧ it.num ≠ 200) :
    committedBytes (writeItems l) = some (writeItems l) :=
  dropFields_writeItems ho fun it hit => by
    have := hd it hit
    simp [this.1, this.2]

/-! ## Parsers -/

/-- What a parser does from position `pos` of `b`: its value and the next position. -/
def pgo {α : Type} (p : Proto.Parser α) (b : ByteArray) (pos : Nat) : Option (α × Nat) :=
  (StateT.run p pos).run b

/-- The monad stack of `Proto.Parser`, unfolded. -/
macro "parser_unfold" : tactic =>
  `(tactic| simp [StateT.run, bind, StateT.bind, ReaderT.run, ReaderT.bind, read, readThe,
    MonadReaderOf.read, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, ReaderT.read, set, StateT.set, pure, ReaderT.pure, failure,
    ReaderT.failure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Option.bind,
    Functor.map, StateT.map, Option.map, StateT.pure, StateT.failure, StateT.run'])

theorem pgo_bind {α β : Type} (p : Proto.Parser α) (f : α → Proto.Parser β) (b : ByteArray)
    (pos : Nat) : pgo (p >>= f) b pos = (pgo p b pos).bind fun (x, q) => pgo (f x) b q := by
  simp only [pgo]
  rfl

theorem pgo_pure {α : Type} (x : α) (b : ByteArray) (pos : Nat) :
    pgo (pure x : Proto.Parser α) b pos = some (x, pos) := rfl

theorem pgo_failure {α : Type} (b : ByteArray) (pos : Nat) :
    pgo (failure : Proto.Parser α) b pos = none := rfl

/-- `Parser.run` is `pgo` from `start`, and must end at the last byte. -/
theorem run_eq {α : Type} (p : Proto.Parser α) (b : ByteArray) (start : Nat) :
    Proto.Parser.run p b start =
      (pgo p b start).bind fun (x, q) => if q = b.size then some x else none := by
  unfold Proto.Parser.run pgo
  rcases h : (StateT.run p start).run b with _ | ⟨x, q⟩
  · parser_unfold
    simp [StateT.run, ReaderT.run] at h
    simp [h]
  · parser_unfold
    simp [StateT.run, ReaderT.run] at h
    simp [h]
    by_cases hq : q = b.size <;> simp [hq] <;> rfl

theorem pgo_take (n : Nat) (b : ByteArray) (pos : Nat) :
    pgo (Proto.Parser.take n) b pos =
      if pos + n ≤ b.size then some (b.extract pos (pos + n), pos + n) else none := by
  unfold pgo Proto.Parser.take
  by_cases h : pos + n ≤ b.size
  · simp only [h, ↓reduceIte]; parser_unfold; simp [h] <;> rfl
  · simp only [h, ↓reduceIte]; parser_unfold; simp [h] <;> rfl

theorem pgo_u8 (b : ByteArray) (pos : Nat) :
    pgo Proto.Parser.u8 b pos = if h : pos < b.size then some (b[pos], pos + 1) else none := by
  unfold pgo Proto.Parser.u8
  by_cases h : pos < b.size
  · simp only [h, ↓reduceDIte]; parser_unfold; simp [h] <;> rfl
  · simp only [h, ↓reduceDIte]; parser_unfold; simp [h] <;> rfl

theorem pgo_u32 (b : ByteArray) (pos : Nat) :
    pgo Proto.Parser.u32 b pos = (readU32? b pos).map fun n => (n, pos + 4) := by
  unfold pgo Proto.Parser.u32
  cases h : readU32? b pos <;> parser_unfold <;> simp [h] <;> rfl

theorem pgo_bytes (b : ByteArray) (pos : Nat) :
    pgo Proto.Parser.bytes b pos = (readU32? b pos).bind fun n =>
      if pos + 4 + n ≤ b.size then some (b.extract (pos + 4) (pos + 4 + n), pos + 4 + n)
      else none := by
  unfold Proto.Parser.bytes
  rw [pgo_bind, pgo_u32]
  cases readU32? b pos <;> simp [pgo_take]

theorem Nonce.ofBytes?_bytes (n : Nonce) : Nonce.ofBytes? n.bytes = some n := by
  simp [Nonce.ofBytes?, n.size_eq]

theorem Nonce.bytes_of_ofBytes? {b : ByteArray} {n : Nonce} (h : Nonce.ofBytes? b = some n) :
    n.bytes = b := by
  unfold Nonce.ofBytes? at h
  split at h
  · cases h; rfl
  · cases h

theorem pgo_nonce (b : ByteArray) (pos : Nat) :
    pgo Proto.Parser.nonce b pos =
      if pos + 32 ≤ b.size then (Nonce.ofBytes? (b.extract pos (pos + 32))).map (·, pos + 32)
      else none := by
  unfold Proto.Parser.nonce
  rw [pgo_bind, pgo_take]
  split
  · simp only [Option.bind_some]
    cases Nonce.ofBytes? (b.extract pos (pos + 32)) <;> rfl
  · rfl

theorem pgo_digests (b : ByteArray) (pos : Nat) :
    pgo Proto.Parser.digests b pos = (readU32? b pos).bind fun n =>
      if pos + 4 + 32 * n ≤ b.size then (readDigests b (pos + 4) #[] n).map (·, pos + 4 + 32 * n)
      else none := by
  unfold Proto.Parser.digests
  rw [pgo_bind, pgo_u32]
  cases readU32? b pos with
  | none => rfl
  | some n =>
    simp only [Option.map_some, Option.bind_some]
    by_cases h : pos + 4 + 32 * n ≤ b.size
    · cases hr : readDigests b (pos + 4) #[] n <;> (unfold pgo; parser_unfold; simp [h, hr]) <;> rfl
    · unfold pgo; parser_unfold; simp [h]; rfl

/-! ### Reading what a writer wrote -/

theorem readU32?_at {b : ByteArray} {pos v : Nat} (h : At b pos (u32be v)) (hv : v < 2 ^ 32) :
    readU32? b pos = some v := by
  have := Encode.readU32?_of_extract (h.extract (At.le_size h (by simp)))
  rwa [Nat.mod_eq_of_lt hv] at this

theorem readU32?_lt {b : ByteArray} {pos v : Nat} (h : readU32? b pos = some v) : v < 2 ^ 32 := by
  unfold readU32? at h
  split at h
  · cases h
    have := b[pos].toNat_lt
    have := b[pos + 1].toNat_lt
    have := b[pos + 2].toNat_lt
    have := b[pos + 3].toNat_lt
    omega
  · cases h

theorem pgo_u32_at {b : ByteArray} {pos v : Nat} (h : At b pos (u32be v)) (hv : v < 2 ^ 32) :
    pgo Proto.Parser.u32 b pos = some (v, pos + 4) := by
  rw [pgo_u32, readU32?_at h hv]; rfl

theorem pgo_u8_at {b : ByteArray} {pos : Nat} {x : UInt8} (h : At b pos ⟨#[x]⟩) :
    pgo Proto.Parser.u8 b pos = some (x, pos + 1) := by
  have h0 := h 0 (show 0 < (⟨#[x]⟩ : ByteArray).size from Nat.zero_lt_one)
  rw [Nat.add_zero] at h0
  have hp : pos < b.size := by
    by_cases hp : pos < b.size
    · exact hp
    · rw [getElem?_neg b pos hp] at h0; cases h0
  rw [pgo_u8, dite_eq_left hp]
  rw [getElem?_pos b pos hp] at h0
  simp only [Option.some.injEq, Prod.mk.injEq, and_true]
  have : (⟨#[x]⟩ : ByteArray)[0]? = some x := rfl
  rw [this, Option.some.injEq] at h0
  exact h0

theorem pgo_take_at {b x : ByteArray} {pos : Nat} (h : At b pos x) (hle : pos + x.size ≤ b.size) :
    pgo (Proto.Parser.take x.size) b pos = some (x, pos + x.size) := by
  rw [pgo_take, ite_eq_left hle, h.extract hle]

theorem pgo_nonce_at {b : ByteArray} {pos : Nat} {n : Nonce} (h : At b pos n.bytes) :
    pgo Proto.Parser.nonce b pos = some (n, pos + 32) := by
  have hle := At.le_size h (by rw [n.size_eq]; decide)
  rw [n.size_eq] at hle
  have hx := h.extract (by rw [n.size_eq]; exact hle)
  rw [n.size_eq] at hx
  rw [pgo_nonce, ite_eq_left hle, hx, Nonce.ofBytes?_bytes]
  rfl

theorem pgo_bytes_at {b v : ByteArray} {pos : Nat} (h : At b pos (Proto.Write.bytes v))
    (hv : v.size < 2 ^ 32) :
    pgo Proto.Parser.bytes b pos = some (v, pos + 4 + v.size) := by
  unfold Proto.Write.bytes at h
  have hend := At.le_size h (by simp only [ByteArray.size_append, Encode.size_u32be]; omega)
  simp only [ByteArray.size_append, Encode.size_u32be] at hend
  have hx := At.right h
  simp only [Encode.size_u32be] at hx
  rw [pgo_bytes, readU32?_at (At.left h) hv]
  simp only [Option.bind_some]
  rw [ite_eq_left (by omega), hx.extract (by omega)]

/-- The digests written one after another sit where `readDigests` reads them. -/
theorem readDigests_at {b : ByteArray} : ∀ (l : List Digest) (off : Nat) (acc : Array Digest),
    At b off (Encode.linksBytesList l) → readDigests b off acc l.length = some (acc ++ l.toArray)
  | [], _, acc, _ => by simp [readDigests]
  | d :: ds, off, acc, h => by
    simp only [Encode.linksBytesList] at h
    have h1 := At.left h
    have h2 := At.right h
    have hle := At.le_size h1 (by rw [d.size_eq]; decide)
    rw [d.size_eq] at hle h2
    have hx := h1.extract (by rw [d.size_eq]; exact hle)
    rw [d.size_eq] at hx
    simp only [List.length_cons, readDigests, hx, Digest.ofBytes?_bytes, Option.bind_eq_bind,
      Option.bind_some]
    rw [readDigests_at ds (off + 32) _ h2]
    simp

theorem write_digests_eq (ds : Array Digest) :
    Proto.Write.digests ds = u32be ds.size ++ linksBytes ds := by
  rw [Proto.Write.digests, ← Array.foldl_toList, Encode.foldl_append_bytes, Encode.linksBytes_eq]

theorem pgo_digests_at {b : ByteArray} {pos : Nat} {ds : Array Digest}
    (h : At b pos (Proto.Write.digests ds)) (hs : ds.size < 2 ^ 32) :
    pgo Proto.Parser.digests b pos = some (ds, pos + 4 + 32 * ds.size) := by
  rw [write_digests_eq] at h
  have hend := At.le_size h (by simp only [ByteArray.size_append, Encode.size_u32be]; omega)
  simp only [ByteArray.size_append, Encode.size_u32be, Encode.size_linksBytes] at hend
  have hx := At.right h
  simp only [Encode.size_u32be, Encode.linksBytes_eq] at hx
  rw [pgo_digests, readU32?_at (At.left h) hs]
  simp only [Option.bind_some]
  rw [ite_eq_left (by omega)]
  have := readDigests_at ds.toList (pos + 4) #[] hx
  simp only [Array.length_toList, Array.toArray_toList, Array.empty_append] at this
  rw [this]
  rfl

/-! ### What a parser read -/

theorem pgo_take_inv {b x : ByteArray} {n pos q : Nat}
    (h : pgo (Proto.Parser.take n) b pos = some (x, q)) :
    q = pos + n ∧ q ≤ b.size ∧ b.extract pos q = x := by
  rw [pgo_take] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by assumption, rfl⟩
  · cases h

theorem pgo_u32_inv {b : ByteArray} {pos q v : Nat} (h : pgo Proto.Parser.u32 b pos = some (v, q)) :
    q = pos + 4 ∧ q ≤ b.size ∧ b.extract pos q = u32be v ∧ v < 2 ^ 32 := by
  rw [pgo_u32] at h
  cases hr : readU32? b pos with
  | none => rw [hr] at h; cases h
  | some w =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hx := Encode.extract_of_readU32? hr
    have hs : pos + 4 ≤ b.size := by
      unfold readU32? at hr; split at hr
      · assumption
      · cases hr
    exact ⟨rfl, hs, hx, readU32?_lt hr⟩

theorem pgo_u8_inv {b : ByteArray} {pos q : Nat} {x : UInt8}
    (h : pgo Proto.Parser.u8 b pos = some (x, q)) :
    q = pos + 1 ∧ q ≤ b.size ∧ b.extract pos q = ⟨#[x]⟩ := by
  rw [pgo_u8] at h
  split at h
  · rename_i hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, hp, ?_⟩
    have hs1 : (b.extract pos (pos + 1)).size = 1 := by simp [ByteArray.size_extract]; omega
    apply ByteArray.ext_getElem (by rw [hs1]; rfl)
    intro i hi hi'
    have : i = 0 := by rw [hs1] at hi; omega
    subst this
    rw [ByteArray.getElem_extract]
    rfl
  · cases h

theorem pgo_nonce_inv {b : ByteArray} {pos q : Nat} {n : Nonce}
    (h : pgo Proto.Parser.nonce b pos = some (n, q)) :
    q = pos + 32 ∧ q ≤ b.size ∧ b.extract pos q = n.bytes := by
  rw [pgo_nonce] at h
  split at h
  · rename_i hp
    cases hn : Nonce.ofBytes? (b.extract pos (pos + 32)) with
    | none => rw [hn] at h; cases h
    | some m =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hp, (Nonce.bytes_of_ofBytes? hn).symm⟩
  · cases h

theorem pgo_bytes_inv {b v : ByteArray} {pos q : Nat}
    (h : pgo Proto.Parser.bytes b pos = some (v, q)) :
    pos ≤ q ∧ q ≤ b.size ∧ b.extract pos q = Proto.Write.bytes v ∧ v.size < 2 ^ 32 := by
  rw [pgo_bytes] at h
  cases hr : readU32? b pos with
  | none => rw [hr] at h; cases h
  | some n =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    split at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hx := Encode.extract_of_readU32? hr
      have hn := readU32?_lt hr
      have hsz : (b.extract (pos + 4) (pos + 4 + n)).size = n := by
        simp [ByteArray.size_extract]; omega
      refine ⟨by omega, hle, ?_, by omega⟩
      unfold Proto.Write.bytes
      rw [hsz, ← hx, ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
        Nat.max_eq_right (by omega)]
    · cases h

theorem pgo_digests_inv {b : ByteArray} {pos q : Nat} {ds : Array Digest}
    (h : pgo Proto.Parser.digests b pos = some (ds, q)) :
    pos ≤ q ∧ q ≤ b.size ∧ b.extract pos q = Proto.Write.digests ds ∧ ds.size < 2 ^ 32 := by
  rw [pgo_digests] at h
  cases hr : readU32? b pos with
  | none => rw [hr] at h; cases h
  | some n =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    split at h
    · rename_i hle
      cases hd : readDigests b (pos + 4) #[] n with
      | none => rw [hd] at h; cases h
      | some res =>
        rw [hd] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ls, hres, hsize, hbytes⟩ := Encode.readDigests_spec hd
        simp only [Array.empty_append] at hres
        subst hres
        have hx := Encode.extract_of_readU32? hr
        have hn := readU32?_lt hr
        refine ⟨by omega, hle, ?_, by omega⟩
        rw [write_digests_eq, hsize, ← hx, hbytes, ByteArray.extract_append_extract,
          Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
    · cases h

/-! ### More about bytes -/

theorem pgo_ite {α : Type} (c : Prop) [Decidable c] (p q : Proto.Parser α) (b : ByteArray)
    (pos : Nat) : pgo (if c then p else q) b pos = if c then pgo p b pos else pgo q b pos := by
  split <;> rfl

theorem size_u8 (x : UInt8) : (Proto.Write.u8 x).size = 1 := rfl

theorem size_write_bytes (b : ByteArray) : (Proto.Write.bytes b).size = 4 + b.size := by
  simp [Proto.Write.bytes, ByteArray.size_append]

theorem size_write_digests (ds : Array Digest) :
    (Proto.Write.digests ds).size = 4 + 32 * ds.size := by
  rw [write_digests_eq, ByteArray.size_append, Encode.size_u32be, Encode.size_linksBytes]

/-- Adjacent pieces of a byte array glue. -/
theorem extract_glue {b : ByteArray} {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    b.extract i j ++ b.extract j k = b.extract i k := by
  rw [ByteArray.extract_append_extract, Nat.min_eq_left hij, Nat.max_eq_right hjk]

/-- `==` on byte arrays is reflexive. -/
theorem beq_self (a : ByteArray) : (a == a) = true := by
  show (a.data == a.data) = true
  exact beq_self_eq_true _

/-- `==` on byte arrays is equality. -/
theorem eq_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  have : (a.data == b.data) = true := h
  exact ByteArray.ext (LawfulBEq.eq_of_beq this)

/-- Two byte strings that both start with a varint below 2^70 agree on it and on the rest. -/
theorem varint_cancel {a b : Nat} {T T' : ByteArray} (h : varint a ++ T = varint b ++ T')
    (ha : a < 2 ^ 70) : a = b ∧ T = T' := by
  have h1 := readVarint_varint_lt (b := varint a ++ T) (i := 0) (At.left (At.self _)) ha
  have h2 := readVarint_varint (b := varint b ++ T') (i := 0) (At.left (At.self _))
  rw [h] at h1
  rw [h1] at h2
  split at h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, -⟩ := h2
    exact ⟨rfl, (ByteArray.append_right_inj _).1 h⟩
  · cases h2

/-- Two byte strings that both start with field `n`, length-delimited, agree on its value (below
2^70 bytes on one side) and on the rest. -/
theorem lenField_cancel {n : Nat} {X Y R R' : ByteArray}
    (h : lenField n X ++ R = lenField n Y ++ R') (hx : X.size < 2 ^ 70) : X = Y ∧ R = R' := by
  simp only [lenField, ByteArray.append_assoc] at h
  have h1 := (ByteArray.append_right_inj _).1 h
  obtain ⟨hs, h2⟩ := varint_cancel h1 hx
  exact (ByteArray.append_eq_append_iff_of_size_eq_left hs).1 h2

/-- The first byte of bytes that start with a varint. -/
theorem getElem?_zero_varint (k : Nat) (T : ByteArray) :
    (varint k ++ T)[0]? = (varint k)[0]? := by
  rw [getElem?_append, ite_eq_left (size_varint_pos k)]

/-- Every field of a written message is one of its items, moved. -/
theorem num_mem_layout {pos : Nat} {l : List Item} {f : Field} (hf : f ∈ layout pos l) :
    ∃ it ∈ l, it.num = f.num := by
  have : f.num ∈ (layout pos l).map (·.num) := List.mem_map_of_mem hf
  rw [map_num_layout] at this
  simpa using this

/-- **The audience of an opening whose message starts with field 201** and holds no other is
that field's value, parsed. -/
theorem audienceOf_items {n : Nonce} {aud : ByteArray} {rest : List Item}
    (ho : ∀ it ∈ Item.len 201 aud :: rest, it.ok) (hr : ∀ it ∈ rest, it.num ≠ 201) :
    Serve.audienceOf (n.bytes ++ writeItems (Item.len 201 aud :: rest)) =
      Serve.parseAudience aud := by
  have hfs := fields_writeItems ho
  have hfilter : ((layout 0 (Item.len 201 aud :: rest)).toArray.filter
      (·.num == Serve.audienceField)).toList =
      [⟨201, 0, (Item.len 201 aud).write.size⟩] := by
    rw [show ∀ (l : List Field) (q : Field → Bool), (l.toArray.filter q).toList = l.filter q
      from fun l q => by simp]
    simp only [layout, Nat.zero_add]
    rw [List.filter_cons_of_pos (by simp [Item.num, Serve.audienceField])]
    rw [List.filter_eq_nil_iff.2]
    · rfl
    · intro f hf
      obtain ⟨it, hit, hnum⟩ := num_mem_layout hf
      have := hr it hit
      simp only [Serve.audienceField, beq_iff_eq]
      omega
  have hat : At (writeItems (Item.len 201 aud :: rest)) 0 (lenField 201 aud) :=
    At.left (At.self (lenField 201 aud ++ writeItems rest))
  unfold Serve.audienceOf
  rw [splitOpening_append]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hfs]
  simp only [Option.bind_some]
  rw [hfilter]
  simp only
  rw [fieldValue_len hat (ho _ (by simp))]
  rfl

/-- An opening made of a nonce and a written message without field 15 or 200 matches its
commitment. -/
theorem openingMatches_items {g : GroupId} {a : Aci} {n : Nonce} {l : List Item}
    (ho : ∀ it ∈ l, it.ok) (hd : ∀ it ∈ l, it.num ≠ 15 ∧ it.num ≠ 200) :
    openingMatches g a (sha256 (commitTag ++ g.bytes ++ a.bytes ++ n.bytes ++ writeItems l))
      (n.bytes ++ writeItems l) = true := by
  unfold openingMatches
  rw [splitOpening_append]
  have hc := committedBytes_writeItems ho hd
  simp [hc, commit]

end Wire

end Zrdt.AppBase
