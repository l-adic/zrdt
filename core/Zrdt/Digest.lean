/-!
# Fixed-size byte strings: `Digest`, `GroupId`, `Aci`

A `Digest` is a SHA-256 output: exactly 32 bytes. A `GroupId` is a Signal group's 32-byte
identifier, and an `Aci` is a Signal account id, 16 bytes. Each is a `ByteArray` together with a
proof of its size, so a value of the wrong length cannot exist.

Digests are ordered byte by byte, the first differing byte deciding (`compare_eq_toList` states
this). The order is lawful (`Std.TransOrd`, `Std.LawfulEqOrd`), which is what `Std.ExtTreeMap`
needs. `GroupId` and `Aci` get the same order.

The comparison is a loop over the bytes. It is proved equal to comparing the byte lists, which is
the specification. (Reading `ByteArray.data` in compiled code copies the array, so the loop avoids
it.)
-/

namespace Zrdt

/-! ## Comparing byte arrays -/

/-- Compare two byte arrays byte by byte. The first byte that differs decides; if one array is a
proper prefix of the other, the shorter one is smaller. -/
def compareBytes (a b : ByteArray) : Ordering :=
  go 0
where
  /-- Compare from position `i` on. -/
  go (i : Nat) : Ordering :=
    if h₁ : a.size ≤ i then
      if b.size ≤ i then .eq else .lt
    else if h₂ : b.size ≤ i then
      .gt
    else
      have h₁ : i < a.size := by omega
      match compare a[i] b[i] with
      | .lt => .lt
      | .eq => go (i + 1)
      | .gt => .gt
  termination_by a.size - i

#guard compareBytes ⟨#[1, 2, 3]⟩ ⟨#[1, 2, 4]⟩ == .lt
#guard compareBytes ⟨#[1, 2, 3]⟩ ⟨#[1, 2]⟩ == .gt
#guard compareBytes ⟨#[9]⟩ ⟨#[9]⟩ == .eq

/-- Dropping `i` bytes, when byte `i` exists, leaves byte `i` in front. -/
theorem drop_data_eq_cons (a : ByteArray) {i : Nat} (h : i < a.size) :
    a.data.toList.drop i = a[i] :: a.data.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact h)]
  simp [ByteArray.getElem_eq_getElem_data]

/-- Dropping at least all bytes leaves nothing. -/
theorem drop_data_eq_nil (a : ByteArray) {i : Nat} (h : a.size ≤ i) :
    a.data.toList.drop i = [] :=
  List.drop_eq_nil_of_le (by rw [Array.length_toList]; exact h)

/-- The loop from position `i` compares what is left of the two byte lists. -/
theorem compareBytes.go_eq (a b : ByteArray) (i : Nat) :
    compareBytes.go a b i = compare (a.data.toList.drop i) (b.data.toList.drop i) := by
  induction i using compareBytes.go.induct a b with
  | case1 i h₁ h₂ =>
    rw [compareBytes.go, dite_eq_left h₁, ite_eq_left h₂, drop_data_eq_nil a h₁,
      drop_data_eq_nil b h₂]
    rfl
  | case2 i h₁ h₂ =>
    rw [compareBytes.go, dite_eq_left h₁, ite_eq_right h₂, drop_data_eq_nil a h₁,
      drop_data_eq_cons b (by omega)]
    rfl
  | case3 i h₁ h₂ =>
    rw [compareBytes.go, dite_eq_right h₁, dite_eq_left h₂, drop_data_eq_cons a (by omega),
      drop_data_eq_nil b h₂]
    rfl
  | case4 i h₁ h₂ _ hc =>
    rw [compareBytes.go, dite_eq_right h₁, dite_eq_right h₂, drop_data_eq_cons a (by omega),
      drop_data_eq_cons b (by omega), List.compare_cons_cons]
    simp [hc]
  | case5 i h₁ h₂ _ hc ih =>
    rw [compareBytes.go, dite_eq_right h₁, dite_eq_right h₂, drop_data_eq_cons a (by omega),
      drop_data_eq_cons b (by omega), List.compare_cons_cons]
    simp [hc, ih]
  | case6 i h₁ h₂ _ hc =>
    rw [compareBytes.go, dite_eq_right h₁, dite_eq_right h₂, drop_data_eq_cons a (by omega),
      drop_data_eq_cons b (by omega), List.compare_cons_cons]
    simp [hc]

/-- The loop computes the lexicographic order of the byte lists. -/
theorem compareBytes_eq_toList (a b : ByteArray) :
    compareBytes a b = compare a.data.toList b.data.toList := by
  rw [compareBytes, compareBytes.go_eq]
  simp

/-- Two byte arrays compare equal exactly when they are equal. -/
theorem compareBytes_eq_eq_iff {a b : ByteArray} : compareBytes a b = .eq ↔ a = b := by
  rw [compareBytes_eq_toList, Std.LawfulEqCmp.compare_eq_iff_eq]
  constructor
  · intro h
    cases a; cases b
    simp_all
  · intro h; rw [h]

instance : Std.TransCmp compareBytes where
  eq_swap {a b} := by
    rw [compareBytes_eq_toList, compareBytes_eq_toList]
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} h₁ h₂ := by
    rw [compareBytes_eq_toList] at h₁ h₂ ⊢
    exact Std.TransCmp.isLE_trans h₁ h₂

instance : Std.LawfulEqCmp compareBytes where
  eq_of_compare h := compareBytes_eq_eq_iff.mp h

/-! ## Hex text, for tests and display -/

/-- Lower-case hex text of a byte array, two characters per byte. -/
def hexOfBytes (b : ByteArray) : String :=
  b.foldl (init := "") fun s x => s.push (digit (x >>> 4)) |>.push (digit (x &&& 15))
where
  /-- The hex character of a value below 16. -/
  digit (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

#guard hexOfBytes ⟨#[0, 9, 10, 255]⟩ == "00090aff"

/-- The value of one hex character (either case), or `none`. -/
def hexValue? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55).toUInt8
  else none

/-- Parse hex text into bytes. `none` on an odd length or a non-hex character. -/
def bytesOfHex? (s : String) : Option ByteArray :=
  go s.toList ByteArray.empty
where
  /-- Parse the remaining characters, appending to `acc`. -/
  go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | hi :: lo :: rest, acc => do
      let h ← hexValue? hi
      let l ← hexValue? lo
      go rest (acc.push (h * 16 + l))
    | [_], _ => none

#guard bytesOfHex? "00090aFF" == some ⟨#[0, 9, 10, 255]⟩
#guard bytesOfHex? "abc" == none
#guard bytesOfHex? "zz" == none

/-! ## `Digest` -/

/-- A SHA-256 output: exactly 32 bytes. -/
structure Digest where
  /-- The 32 bytes. -/
  bytes : ByteArray
  /-- There are exactly 32 of them. -/
  size_eq : bytes.size = 32
deriving DecidableEq

namespace Digest

/-- The digest whose 32 bytes are all zero. -/
def zero : Digest := ⟨⟨Array.replicate 32 0⟩, rfl⟩

instance : Inhabited Digest := ⟨zero⟩

/-- A digest from a byte array, if it has exactly 32 bytes. -/
def ofBytes? (b : ByteArray) : Option Digest :=
  if h : b.size = 32 then some ⟨b, h⟩ else none

/-- `ofBytes?` gives back a value from its own bytes. -/
@[simp] theorem ofBytes?_bytes (d : Digest) : ofBytes? d.bytes = some d := by
  simp [ofBytes?, d.size_eq]

/-- What `ofBytes?` returns has exactly the bytes it was given. -/
theorem bytes_of_ofBytes? {b : ByteArray} {d : Digest} (h : ofBytes? b = some d) :
    d.bytes = b := by
  unfold ofBytes? at h; split at h <;> cases h; rfl

/-- A digest from 64 hex characters. -/
def ofHex? (s : String) : Option Digest :=
  bytesOfHex? s >>= ofBytes?

/-- Lower-case hex text, 64 characters. -/
def toHex (d : Digest) : String := hexOfBytes d.bytes

instance : ToString Digest := ⟨toHex⟩
instance : Repr Digest := ⟨fun d _ => "Digest " ++ repr d.toHex⟩
instance : Hashable Digest := ⟨fun d => hash d.bytes⟩

/-- Digests are ordered byte by byte (see `compare_eq_toList`). -/
instance : Ord Digest := ⟨fun a b => compareBytes a.bytes b.bytes⟩

/-- The specification of the order: compare the byte lists lexicographically. -/
theorem compare_eq_toList (a b : Digest) :
    compare a b = compare a.bytes.data.toList b.bytes.data.toList :=
  compareBytes_eq_toList a.bytes b.bytes

/-- Two digests are equal exactly when their bytes are. -/
theorem ext_bytes {a b : Digest} (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; cases h; rfl

instance : Std.TransOrd Digest where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := compareBytes)
  isLE_trans h₁ h₂ := Std.TransCmp.isLE_trans (cmp := compareBytes) h₁ h₂

instance : Std.LawfulEqOrd Digest where
  eq_of_compare h := ext_bytes (Std.LawfulEqCmp.eq_of_compare (cmp := compareBytes) h)

example : (zero.toHex).length = 64 := by decide
#guard zero.toHex == "0000000000000000000000000000000000000000000000000000000000000000"
#guard (ofHex? (String.ofList (List.replicate 64 'a'))).isSome
#guard (ofHex? "00").isNone
#guard compare (ofHex? ("01" ++ String.ofList (List.replicate 62 '0'))).get!
    (ofHex? ("00" ++ String.ofList (List.replicate 62 'f'))).get! == .gt

end Digest

/-! ## `GroupId` -/

/-- A Signal group's identifier: exactly 32 bytes. -/
structure GroupId where
  /-- The 32 bytes. -/
  bytes : ByteArray
  /-- There are exactly 32 of them. -/
  size_eq : bytes.size = 32
deriving DecidableEq

namespace GroupId

/-- The group id whose 32 bytes are all zero. -/
def zero : GroupId := ⟨⟨Array.replicate 32 0⟩, rfl⟩

instance : Inhabited GroupId := ⟨zero⟩

/-- A group id from a byte array, if it has exactly 32 bytes. -/
def ofBytes? (b : ByteArray) : Option GroupId :=
  if h : b.size = 32 then some ⟨b, h⟩ else none

/-- `ofBytes?` gives back a value from its own bytes. -/
@[simp] theorem ofBytes?_bytes (g : GroupId) : ofBytes? g.bytes = some g := by
  simp [ofBytes?, g.size_eq]

/-- What `ofBytes?` returns has exactly the bytes it was given. -/
theorem bytes_of_ofBytes? {b : ByteArray} {g : GroupId} (h : ofBytes? b = some g) :
    g.bytes = b := by
  unfold ofBytes? at h; split at h <;> cases h; rfl

/-- A group id from 64 hex characters. -/
def ofHex? (s : String) : Option GroupId :=
  bytesOfHex? s >>= ofBytes?

/-- Lower-case hex text, 64 characters. -/
def toHex (g : GroupId) : String := hexOfBytes g.bytes

instance : ToString GroupId := ⟨toHex⟩
instance : Repr GroupId := ⟨fun g _ => "GroupId " ++ repr g.toHex⟩
instance : Hashable GroupId := ⟨fun g => hash g.bytes⟩

/-- Group ids are ordered byte by byte, like digests. -/
instance : Ord GroupId := ⟨fun a b => compareBytes a.bytes b.bytes⟩

/-- Two group ids are equal exactly when their bytes are. -/
theorem ext_bytes {a b : GroupId} (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; cases h; rfl

instance : Std.TransOrd GroupId where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := compareBytes)
  isLE_trans h₁ h₂ := Std.TransCmp.isLE_trans (cmp := compareBytes) h₁ h₂

instance : Std.LawfulEqOrd GroupId where
  eq_of_compare h := ext_bytes (Std.LawfulEqCmp.eq_of_compare (cmp := compareBytes) h)

#guard (ofBytes? ⟨Array.replicate 32 7⟩).isSome
#guard (ofBytes? ⟨Array.replicate 16 7⟩).isNone

end GroupId

/-! ## `Aci` -/

/-- A Signal account id (ACI): exactly 16 bytes. -/
structure Aci where
  /-- The 16 bytes. -/
  bytes : ByteArray
  /-- There are exactly 16 of them. -/
  size_eq : bytes.size = 16
deriving DecidableEq

namespace Aci

/-- The account id whose 16 bytes are all zero. -/
def zero : Aci := ⟨⟨Array.replicate 16 0⟩, rfl⟩

instance : Inhabited Aci := ⟨zero⟩

/-- An account id from a byte array, if it has exactly 16 bytes. -/
def ofBytes? (b : ByteArray) : Option Aci :=
  if h : b.size = 16 then some ⟨b, h⟩ else none

/-- `ofBytes?` gives back a value from its own bytes. -/
@[simp] theorem ofBytes?_bytes (a : Aci) : ofBytes? a.bytes = some a := by
  simp [ofBytes?, a.size_eq]

/-- What `ofBytes?` returns has exactly the bytes it was given. -/
theorem bytes_of_ofBytes? {b : ByteArray} {a : Aci} (h : ofBytes? b = some a) :
    a.bytes = b := by
  unfold ofBytes? at h; split at h <;> cases h; rfl

/-- An account id from 32 hex characters. -/
def ofHex? (s : String) : Option Aci :=
  bytesOfHex? s >>= ofBytes?

/-- Lower-case hex text, 32 characters. -/
def toHex (a : Aci) : String := hexOfBytes a.bytes

instance : ToString Aci := ⟨toHex⟩
instance : Repr Aci := ⟨fun a _ => "Aci " ++ repr a.toHex⟩
instance : Hashable Aci := ⟨fun a => hash a.bytes⟩

/-- Account ids are ordered byte by byte, like digests. -/
instance : Ord Aci := ⟨fun a b => compareBytes a.bytes b.bytes⟩

/-- Two account ids are equal exactly when their bytes are. -/
theorem ext_bytes {a b : Aci} (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; cases h; rfl

instance : Std.TransOrd Aci where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := compareBytes)
  isLE_trans h₁ h₂ := Std.TransCmp.isLE_trans (cmp := compareBytes) h₁ h₂

instance : Std.LawfulEqOrd Aci where
  eq_of_compare h := ext_bytes (Std.LawfulEqCmp.eq_of_compare (cmp := compareBytes) h)

#guard (ofHex? "000102030405060708090a0b0c0d0e0f").map toHex ==
  some "000102030405060708090a0b0c0d0e0f"
#guard (ofBytes? ⟨Array.replicate 32 7⟩).isNone

end Aci

end Zrdt
