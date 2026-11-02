import Zrdt.Apps

/-!
# Piece stores and the torrent: what they guarantee (docs/apps/BUILD_M1.md §C.2)

**Owner: lane torrent.** The piece-store theorems, about lane base's definitions (`Zrdt.AppBase`)
and the dispatcher (`Zrdt.Apps`), and the torrent theorems, about `Zrdt.Torrent`; without
Mathlib. They guard the bulk data of both apps. `zrdtd` does not import this module, so it is not
part of `Apps.sources` (the build text of `VERSION`).

- **Encodings** (`Zrdt.PieceProofs`): `pieceOk_unique` (one index, one piece), `bindCtx_unique`
  (one announcement, one context), `assemble_unique` (everyone who completes holds the same
  bytes), and the lemmas they rest on (`record_eq`, `opening_eq`, `eq_of_slices`, ...).
- **The torrent** (`Zrdt.Torrent`): `btBuild_binds` (the author's announcement binds),
  `btBuild_complete` (any bind of it accepts exactly her file), `run_btFile` (`BT_FILE` answers
  only from a bound torrent context, with a canonical manifest and a safe name).

Every collision disjunct is `AppBase.Sha256Collision`: two different byte strings with one
SHA-256. A record-digest collision is one, through `decode_encode` (`record_eq`).
-/

namespace Zrdt.PieceProofs

open AppBase

/-- `ByteArray`'s `==` compares the bytes (it has no `LawfulBEq` instance). -/
theorem bytes_beq {a b : ByteArray} : (a == b) = true ↔ a = b := by
  show (a.data == b.data) = true ↔ a = b
  simp [ByteArray.ext_iff]

/-- **What a bind is.** `bindCtx` succeeds exactly when the opening matches A, commits a canonical
app message of the requested app whose channel id is A's group, with a well-formed descriptor and a
well-formed audience; the context is then made of A and of what the opening commits, nothing else. -/
theorem bindCtx_ok {sg : GroupId} {app : ByteArray} {A : Rec} {o : ByteArray} {c : PieceCtx}
    (h : bindCtx sg app A o = .ok c) :
    openingMatches A.group A.author A.commit o = true ∧
    ∃ hd db d seats, appOf o = some hd ∧ hd.app = app ∧ channelId sg hd.app hd.channel = A.group ∧
      hd.descriptor = some db ∧ Descriptor.parse db = some d ∧ d.wellFormed = true ∧
      Serve.parseAudience hd.audience = some seats ∧
      c = ⟨hashRecord A, A.group, A.author, hd, seats, d⟩ := by
  unfold bindCtx at h
  by_cases hm : openingMatches A.group A.author A.commit o = true
  · refine ⟨hm, ?_⟩
    simp only [hm] at h
    cases ha : appOf o with
    | none => simp only [ha] at h; cases h
    | some hd =>
      simp only [ha] at h
      by_cases hc : (hd.app == app && channelId sg hd.app hd.channel == A.group) = true
      · simp only [hc] at h
        cases hdb : hd.descriptor with
        | none => simp only [hdb] at h; cases h
        | some db =>
          cases hp : Descriptor.parse db with
          | none => simp only [hdb, hp] at h; cases h
          | some d =>
            by_cases hw : d.wellFormed = true
            · cases hs : Serve.parseAudience hd.audience with
              | none => simp only [hdb, hp, hw, hs] at h; cases h
              | some seats =>
                simp only [hdb, hp, hw, hs] at h
                cases h
                simp only [Bool.and_eq_true, beq_iff_eq] at hc
                exact ⟨hd, db, d, seats, rfl, bytes_beq.1 hc.1, hc.2, hdb, hp, hw, hs, rfl⟩
            · simp only [hdb, hp, hw] at h; cases h
      · simp only [hc] at h; cases h
  · simp only [hm] at h; cases h

/-- Two records with one digest are one record, or SHA-256 has a collision (through
`decode_encode`). -/
theorem record_eq {r₁ r₂ : Rec} (h : hashRecord r₁ = hashRecord r₂) : r₁ = r₂ ∨ Sha256Collision := by
  by_cases he : encode r₁ = encode r₂
  · left
    have := decode_encode r₁
    rw [he, decode_encode] at this
    exact (Option.some.inj this).symm
  · exact .inr ⟨_, _, he, h⟩

/-- One commitment, one committed message (same group, author and nonce), or a collision. -/
theorem commitOf_eq {g : GroupId} {a : Aci} {n : Nonce} {m₁ m₂ : ByteArray}
    (h : commitOf g a n m₁ = commitOf g a n m₂) : m₁ = m₂ ∨ Sha256Collision := by
  unfold commitOf at h
  by_cases hx : commitTag ++ g.bytes ++ a.bytes ++ n.bytes ++ m₁ =
      commitTag ++ g.bytes ++ a.bytes ++ n.bytes ++ m₂
  · exact .inl ((ByteArray.append_right_inj _).1 hx)
  · exact .inr ⟨_, _, hx, h⟩

/-- **One record, one opening.** Two openings that match one commitment (one group, one author)
are one opening, or SHA-256 has a collision (lane base's `opening_bound`, proved here for the
piece-store theorems). -/
theorem opening_eq {g : GroupId} {a : Aci} {c : Digest} {o₁ o₂ : ByteArray}
    (h₁ : openingMatches g a c o₁ = true) (h₂ : openingMatches g a c o₂ = true) :
    o₁ = o₂ ∨ Sha256Collision := by
  obtain ⟨n₁, m₁, rfl, hb₁, hc₁⟩ := openingMatches_spec h₁
  obtain ⟨n₂, m₂, rfl, hb₂, hc₂⟩ := openingMatches_spec h₂
  simp only [commit, hb₁, hb₂, Option.map_some, Option.some.injEq] at hc₁ hc₂
  let P := commitTag ++ g.bytes ++ a.bytes
  have e₁ : commitTag ++ g.bytes ++ a.bytes ++ n₁.bytes ++ m₁ = P ++ (n₁.bytes ++ m₁) :=
    ByteArray.append_assoc
  have e₂ : commitTag ++ g.bytes ++ a.bytes ++ n₂.bytes ++ m₂ = P ++ (n₂.bytes ++ m₂) :=
    ByteArray.append_assoc
  rw [e₁] at hc₁
  rw [e₂] at hc₂
  by_cases hx : P ++ (n₁.bytes ++ m₁) = P ++ (n₂.bytes ++ m₂)
  · exact .inl ((ByteArray.append_right_inj P).1 hx)
  · exact .inr ⟨_, _, hx, hc₁.trans hc₂.symm⟩

/-- A piece's committed bytes determine its bytes, among bytes of one length. -/
theorem pieceMessage_inj {aud : ByteArray} {i : Nat} {b₁ b₂ : ByteArray} (hs : b₁.size = b₂.size)
    (h : pieceMessage aud i b₁ = pieceMessage aud i b₂) : b₁ = b₂ := by
  simp only [pieceMessage, lenField, hs, ← ByteArray.append_assoc] at h
  exact (ByteArray.append_right_inj _).1 h

/-- What `pieceOk` checks. -/
theorem pieceOk_iff {c : PieceCtx} {i : Nat} {b : ByteArray} :
    pieceOk c i b = true ↔ ∃ d, c.desc.ordered[i]? = some d ∧
      b.size = pieceLen c.desc.exp c.desc.len i ∧ hashRecord (pieceRecord c i b) = d := by
  unfold pieceOk
  cases hd : c.desc.ordered[i]? with
  | none => simp
  | some d => simp [Bool.and_eq_true, beq_iff_eq]

/-- **One index, one piece.** Two byte strings that both pass `pieceOk` at index `i` of one context
are equal, or SHA-256 has a collision. -/
theorem pieceOk_unique {c : PieceCtx} {i : Nat} {b₁ b₂ : ByteArray}
    (h₁ : pieceOk c i b₁ = true) (h₂ : pieceOk c i b₂ = true) : b₁ = b₂ ∨ Sha256Collision := by
  obtain ⟨d₁, hd₁, hs₁, hr₁⟩ := pieceOk_iff.1 h₁
  obtain ⟨d₂, hd₂, hs₂, hr₂⟩ := pieceOk_iff.1 h₂
  rw [hd₁, Option.some.injEq] at hd₂
  subst hd₂
  rcases record_eq (hr₁.trans hr₂.symm) with hr | hr
  · have hc := congrArg Rec.commit hr
    simp only [pieceRecord, Rec.commit_make] at hc
    rcases commitOf_eq hc with hm | hm
    · exact .inl (pieceMessage_inj (hs₁.trans hs₂.symm) hm)
    · exact .inr hm
  · exact .inr hr

/-- **One announcement, one context.** Two binds of announcements with one digest (by any devices,
with any Signal group and app they were asked for) give one context, or SHA-256 has a collision. -/
theorem bindCtx_unique {sg₁ sg₂ : GroupId} {p₁ p₂ o₁ o₂ : ByteArray} {A₁ A₂ : Rec}
    {c₁ c₂ : PieceCtx} (hA : hashRecord A₁ = hashRecord A₂)
    (h₁ : bindCtx sg₁ p₁ A₁ o₁ = .ok c₁) (h₂ : bindCtx sg₂ p₂ A₂ o₂ = .ok c₂) :
    c₁ = c₂ ∨ Sha256Collision := by
  rcases record_eq hA with rfl | hc
  · obtain ⟨hm₁, hd₁, db₁, d₁, s₁, ha₁, -, -, hdb₁, hp₁, -, hs₁, rfl⟩ := bindCtx_ok h₁
    obtain ⟨hm₂, hd₂, db₂, d₂, s₂, ha₂, -, -, hdb₂, hp₂, -, hs₂, rfl⟩ := bindCtx_ok h₂
    rcases opening_eq hm₁ hm₂ with rfl | hc
    · rw [ha₁, Option.some.injEq] at ha₂
      subst ha₂
      rw [hdb₁, Option.some.injEq] at hdb₂
      subst hdb₂
      rw [hp₁, Option.some.injEq] at hp₂
      subst hp₂
      rw [hs₁, Option.some.injEq] at hs₂
      subst hs₂
      exact .inl rfl
    · exact .inr hc
  · exact .inr hc

/-- A slice has its piece's length: 2^k, except the last. -/
theorem size_slice (k : Nat) (s : ByteArray) (i : Nat) :
    (slice k s i).size = pieceLen k s.size i := by
  simp only [slice, pieceLen, ByteArray.size_extract, Nat.succ_mul]
  generalize i * 2 ^ k = x
  generalize 2 ^ k = P
  omega

/-- N = ⌈L / 2^k⌉ pieces cover the stream. -/
theorem le_pieceCount_mul (k L : Nat) : L ≤ pieceCount k L * 2 ^ k := by
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  unfold pieceCount
  have h1 := Nat.div_add_mod (L + 2 ^ k - 1) (2 ^ k)
  have h2 := Nat.mod_lt (L + 2 ^ k - 1) hp
  rw [Nat.mul_comm] at h1
  omega

/-- Equal first `n` slices: equal first `n · 2^k` bytes. -/
theorem extract_prefix {k : Nat} {s₁ s₂ : ByteArray} :
    ∀ n, (∀ i < n, slice k s₁ i = slice k s₂ i) → s₁.extract 0 (n * 2 ^ k) = s₂.extract 0 (n * 2 ^ k)
  | 0, _ => by simp
  | n + 1, h => by
    have hle : n * 2 ^ k ≤ (n + 1) * 2 ^ k := Nat.mul_le_mul_right _ (Nat.le_succ n)
    rw [ByteArray.extract_eq_extract_append_extract (n * 2 ^ k) (Nat.zero_le _) hle,
      ByteArray.extract_eq_extract_append_extract (a := s₂) (n * 2 ^ k) (Nat.zero_le _) hle,
      extract_prefix n (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    exact congrArg _ (h n (Nat.lt_succ_self n))

/-- Two streams of one length with equal slices are equal. -/
theorem eq_of_slices {k : Nat} {s₁ s₂ : ByteArray} (hs : s₁.size = s₂.size)
    (h : ∀ i < pieceCount k s₁.size, slice k s₁ i = slice k s₂ i) : s₁ = s₂ := by
  have hp := extract_prefix _ h
  have h₁ := le_pieceCount_mul k s₁.size
  have h₂ : s₂.size ≤ pieceCount k s₁.size * 2 ^ k := hs ▸ h₁
  have e₁ : s₁.extract 0 (pieceCount k s₁.size * 2 ^ k) = s₁ := by
    rw [← Nat.max_eq_left h₁]; exact ByteArray.extract_zero_max_size
  have e₂ : s₂.extract 0 (pieceCount k s₁.size * 2 ^ k) = s₂ := by
    rw [← Nat.max_eq_left h₂]; exact ByteArray.extract_zero_max_size
  rwa [e₁, e₂] at hp


/-- What `assembleOk` checks. -/
theorem assembleOk_iff {c : PieceCtx} {s : ByteArray} :
    assembleOk c s = true ↔
      s.size = c.desc.len ∧ ∀ i < c.count, pieceOk c i (slice c.desc.exp s i) = true := by
  simp [assembleOk, List.all_eq_true, List.mem_range]

/-- A well-formed descriptor lists N = ⌈L / 2^k⌉ digests. -/
theorem count_of_wellFormed {d : Descriptor} (hw : d.wellFormed = true) :
    d.ordered.size = pieceCount d.exp d.len := by
  simp only [Descriptor.wellFormed, Bool.and_eq_true, beq_iff_eq] at hw
  exact hw.1.1.2

/-- **Everyone who completes holds the same bytes** (BUILD_M1 §C.2, advertised). Two streams that
pass `assembleOk` under contexts bound from announcements with one digest are equal, or SHA-256
has a collision. Each device binds on its own (any Signal group, app, opening it was given). -/
theorem assemble_unique {sg₁ sg₂ : GroupId} {p₁ p₂ o₁ o₂ s₁ s₂ : ByteArray} {A₁ A₂ : Rec}
    {c₁ c₂ : PieceCtx} (hA : hashRecord A₁ = hashRecord A₂)
    (h₁ : bindCtx sg₁ p₁ A₁ o₁ = .ok c₁) (h₂ : bindCtx sg₂ p₂ A₂ o₂ = .ok c₂)
    (hs₁ : assembleOk c₁ s₁ = true) (hs₂ : assembleOk c₂ s₂ = true) : s₁ = s₂ ∨ Sha256Collision := by
  rcases bindCtx_unique hA h₁ h₂ with rfl | hc
  · obtain ⟨-, _, _, d, _, -, -, -, -, -, hw, -, rfl⟩ := bindCtx_ok h₁
    obtain ⟨hl₁, hp₁⟩ := assembleOk_iff.1 hs₁
    obtain ⟨hl₂, hp₂⟩ := assembleOk_iff.1 hs₂
    by_cases hC : Sha256Collision
    · exact .inr hC
    · refine .inl (eq_of_slices (k := d.exp) (hl₁.trans hl₂.symm) fun i hi => ?_)
      have hi' : i < d.ordered.size := by rw [count_of_wellFormed hw, ← hl₁]; exact hi
      rcases pieceOk_unique (hp₁ i hi') (hp₂ i hi') with h | h
      · exact h
      · exact absurd h hC
  · exact .inr hc


/-- `==` on optional byte arrays compares them. -/
theorem opt_bytes_beq {a b : Option ByteArray} : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> simp [bytes_beq]

/-- The converse of `bindCtx_ok`: when every check passes, `bindCtx` gives this context. -/
theorem bindCtx_of {sg : GroupId} {app : ByteArray} {A : Rec} {o : ByteArray} {hd : AppHeader}
    {db : ByteArray} {d : Descriptor} {seats : Array Serve.Seat}
    (hm : openingMatches A.group A.author A.commit o = true) (ha : appOf o = some hd)
    (happ : hd.app = app) (hch : channelId sg hd.app hd.channel = A.group)
    (hdb : hd.descriptor = some db) (hp : Descriptor.parse db = some d) (hw : d.wellFormed = true)
    (hs : Serve.parseAudience hd.audience = some seats) :
    bindCtx sg app A o = .ok ⟨hashRecord A, A.group, A.author, hd, seats, d⟩ := by
  have hc : (hd.app == app && channelId sg hd.app hd.channel == A.group) = true := by
    simp [bytes_beq.2 happ, hch]
  unfold bindCtx
  simp only [hm, ha, hc, hdb, hp, hw, hs]
  rfl

/-- The app message of an opening is that of its committed bytes. -/
theorem appOf_opening (n : Nonce) (m : ByteArray) : appOf (n.bytes ++ m) = appHeader m := by
  simp [appOf, splitOpening_append]

/-- `readsBack` means the descriptor's bytes parse to it. -/
theorem readsBack_spec {d : Descriptor} (h : Torrent.readsBack d = true) :
    Descriptor.parse d.write = some d := by
  unfold Torrent.readsBack at h
  split at h
  · rename_i d' hp
    rw [hp]
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨⟨nb, ns⟩, l, k, ds, m⟩ := d
    obtain ⟨⟨nb', ns'⟩, l', k', ds', m'⟩ := d'
    have e1 := bytes_beq.1 h1
    have e5 := bytes_beq.1 h5
    simp only at e1 h2 h3 h4 e5
    subst e1 h2 h3 h4 e5
    rfl
  · cases h

/-- `sliceDigests` lists the digest of each slice, at its index. -/
theorem getElem?_sliceDigests {c : PieceCtx} {s : ByteArray} {i : Nat}
    (hi : i < pieceCount c.desc.exp s.size) :
    (Torrent.sliceDigests c s)[i]? = some (hashRecord (pieceRecord c i (slice c.desc.exp s i))) := by
  simp [Torrent.sliceDigests, hi]

/-- `sliceDigests` lists N = ⌈L / 2^k⌉ digests. -/
theorem size_sliceDigests (c : PieceCtx) (s : ByteArray) :
    (Torrent.sliceDigests c s).size = pieceCount c.desc.exp s.size := by
  simp [Torrent.sliceDigests]

end Zrdt.PieceProofs

namespace Zrdt.Torrent
open AppBase PieceProofs

/-- **What `BT_BUILD` returns.** Its `OK` is the app message of `header` with the descriptor
(nonce, L, k, the slices' digests, `manifestOf name L`), and every read-back check passed. -/
theorem btBuild_spec {ch : GroupId} {a : Aci} {nc : Nonce} {e : Nat} {aud ptrs s msg : ByteArray}
    {name : String} {ord : Array Digest}
    (hb : btBuild ch a nc e aud name ptrs s = .ok (msg, ord)) :
    ∃ seats, Serve.parseAudience aud = some seats ∧
      ord = sliceDigests (buildCtx ch a nc e aud seats s.size (manifestOf name s.size)) s ∧
      msg = appMessage (header aud ptrs (some (Descriptor.write
        ⟨nc, s.size, e, ord, manifestOf name s.size⟩))) ∧
      safeComponent name = true ∧
      Descriptor.wellFormed ⟨nc, s.size, e, ord, manifestOf name s.size⟩ = true ∧
      appHeader msg = some (header aud ptrs (some (Descriptor.write
        ⟨nc, s.size, e, ord, manifestOf name s.size⟩))) ∧
      committedBytes msg = some msg ∧
      readsBack ⟨nc, s.size, e, ord, manifestOf name s.size⟩ = true := by
  unfold btBuild at hb
  by_cases hn : safeComponent name = true
  · by_cases hl : (pieceExpOk e && 1 ≤ s.size && s.size ≤ maxPieces * 2 ^ e &&
        ptrs.size ≤ maxPointers) = true
    · cases hs : Serve.parseAudience aud with
      | none => simp only [hn, hl, hs] at hb; cases hb
      | some seats =>
        by_cases hg : (Descriptor.wellFormed ⟨nc, s.size, e, sliceDigests (buildCtx ch a nc e aud
              seats s.size (manifestOf name s.size)) s, manifestOf name s.size⟩ &&
            (header aud ptrs (some (Descriptor.write ⟨nc, s.size, e, sliceDigests (buildCtx ch a nc e
              aud seats s.size (manifestOf name s.size)) s, manifestOf name s.size⟩))).wellFormed &&
            appHeader (appMessage (header aud ptrs (some (Descriptor.write ⟨nc, s.size, e,
              sliceDigests (buildCtx ch a nc e aud seats s.size (manifestOf name s.size)) s,
              manifestOf name s.size⟩)))) == some (header aud ptrs (some (Descriptor.write
              ⟨nc, s.size, e, sliceDigests (buildCtx ch a nc e aud seats s.size
              (manifestOf name s.size)) s, manifestOf name s.size⟩))) &&
            committedBytes (appMessage (header aud ptrs (some (Descriptor.write ⟨nc, s.size, e,
              sliceDigests (buildCtx ch a nc e aud seats s.size (manifestOf name s.size)) s,
              manifestOf name s.size⟩)))) == some (appMessage (header aud ptrs (some
              (Descriptor.write ⟨nc, s.size, e, sliceDigests (buildCtx ch a nc e aud seats s.size
              (manifestOf name s.size)) s, manifestOf name s.size⟩)))) &&
            readsBack ⟨nc, s.size, e, sliceDigests (buildCtx ch a nc e aud seats s.size
              (manifestOf name s.size)) s, manifestOf name s.size⟩) = true
        · simp only [hn, hl, hs, hg] at hb
          cases hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hg
          obtain ⟨⟨⟨⟨hw, -⟩, hh⟩, hc⟩, hr⟩ := hg
          refine ⟨seats, rfl, rfl, rfl, hn, hw, hh, opt_bytes_beq.1 hc, hr⟩
        · simp only [hn, hl, hs, hg] at hb; cases hb
    · simp only [hn, hl] at hb; cases hb
  · simp only [hn] at hb; cases hb


/-- **The author's announcement binds** (BUILD_M1 §C.2). Committed with any nonce `n` and links,
in the channel `bt/files` of the Signal group, `BT_BUILD`'s message gives an announcement that
`bindCtx` accepts. -/
theorem btBuild_binds {ch sg : GroupId} {a : Aci} {nc n : Nonce} {e : Nat}
    {aud ptrs s msg : ByteArray} {name : String} {ord ls : Array Digest}
    (hb : btBuild ch a nc e aud name ptrs s = .ok (msg, ord))
    (hch : ch = channelId sg appTorrent channelTorrent) :
    ∃ ctx, bindCtx sg appTorrent (Rec.make ch (commitOf ch a n msg) ls a) (n.bytes ++ msg) =
      .ok ctx := by
  obtain ⟨seats, hs, -, -, -, hw, hh, hc, hr⟩ := btBuild_spec hb
  refine ⟨_, bindCtx_of (hd := header aud ptrs (some (Descriptor.write
    ⟨nc, s.size, e, ord, manifestOf name s.size⟩))) ?_ ?_ rfl ?_ rfl (readsBack_spec hr) hw hs⟩
  · simp only [Rec.group_make, Rec.author_make, Rec.commit_make]
    unfold openingMatches
    rw [splitOpening_append]
    simp [hc, commit, commitOf]
  · rw [appOf_opening, hh]
  · simp [header, hch]

/-- **The author's own announcement makes her file fetchable** (BUILD_M1 §C.2, advertised). Any
bind of the announcement `BT_BUILD` built (committed with any nonce `n` and links `ls`) accepts
the author's stream `s` (`assembleOk`), and its piece digests are the ones `BT_BUILD` returned.
`nc`: the store nonce; `e`: log₂ of the piece size. -/
theorem btBuild_complete {ch sg : GroupId} {a : Aci} {nc n : Nonce} {e : Nat}
    {aud ptrs s msg : ByteArray} {name : String} {ord : Array Digest} {ls : Array Digest}
    {ctx : PieceCtx} (hb : btBuild ch a nc e aud name ptrs s = .ok (msg, ord))
    (hbind : bindCtx sg appTorrent (Rec.make ch (commitOf ch a n msg) ls a) (n.bytes ++ msg) =
      .ok ctx) :
    assembleOk ctx s = true ∧ ctx.desc.ordered = ord := by
  obtain ⟨seats, hs, hord, -, -, hw, hh, -, hr⟩ := btBuild_spec hb
  obtain ⟨-, hd, db, d, seats', ha, -, -, hdb, hp, -, hs', rfl⟩ := bindCtx_ok hbind
  rw [appOf_opening, hh, Option.some.injEq] at ha
  subst ha
  simp only [header, Option.some.injEq] at hdb
  subst hdb
  rw [readsBack_spec hr, Option.some.injEq] at hp
  subst hp
  simp only [header] at hs'
  rw [hs, Option.some.injEq] at hs'
  subst hs'
  refine ⟨assembleOk_iff.2 ⟨rfl, fun i hi => pieceOk_iff.2 ⟨_, ?_, size_slice e s i, rfl⟩⟩, rfl⟩
  have hi' : i < pieceCount e s.size := by
    simpa [PieceCtx.count, hord, size_sliceDigests, buildCtx] using hi
  simp only
  rw [hord, getElem?_sliceDigests (by simpa [buildCtx] using hi')]
  rfl


/-- **`BT_FILE`** answers only from a bound torrent context: its manifest is exactly
`manifestOf` of the name and of the descriptor's L, and the name is a safe path component. -/
theorem run_btFile {s : State} {key name : String} {len : Nat}
    (h : run s (.file key) = .file name len) :
    ∃ ctx, s.ctxs[key]? = some ctx ∧ ctx.header.app = appTorrent ∧ ctx.desc.len = len ∧
      ctx.desc.manifest = manifestOf name len ∧ safeComponent name = true := by
  simp only [run] at h
  cases hc : s.ctxs[key]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc] at h
    refine ⟨c, rfl, ?_⟩
    unfold fileOf at h
    by_cases ha : c.header.app = appTorrent
    · have ha' : (c.header.app != appTorrent) = false := by simp [bne, bytes_beq.2 ha]
      simp only [ha', Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · cases h
      · rename_i n l _
        by_cases hl : l = c.desc.len ∧ manifestOf n l = c.desc.manifest
        · have hl' : (l != c.desc.len || manifestOf n l != c.desc.manifest) = false := by
            have hm := bytes_beq.2 hl.2
            rw [hl.1] at hm
            simp [bne, hl.1, hm]
          simp only [hl', Bool.false_eq_true, ↓reduceIte] at h
          by_cases hs : safeComponent n = true
          · simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Reply.file.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨ha, hl.1.symm, hl.2.symm, hs⟩
          · simp [hs] at h
        · have hl' : (l != c.desc.len || manifestOf n l != c.desc.manifest) = true := by
            by_cases h0 : l = c.desc.len
            · have h1 : ¬ manifestOf n l = c.desc.manifest := fun h2 => hl ⟨h0, h2⟩
              simp only [Bool.or_eq_true, bne, Bool.not_eq_true']
              right
              cases hb : (manifestOf n l == c.desc.manifest)
              · rfl
              · exact absurd (bytes_beq.1 hb) h1
            · simp [bne, h0]
          simp [hl'] at h
    · have ha' : (c.header.app != appTorrent) = true := by
        simp only [bne, Bool.not_eq_true']
        cases hb : (c.header.app == appTorrent)
        · rfl
        · exact absurd (bytes_beq.1 hb) ha
      simp [ha'] at h

end Zrdt.Torrent
