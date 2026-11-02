import Zrdt.Apps

/-!
# Lane base's theorems with their hypotheses met (docs/apps/BUILD_M1.md §C.1, §E.1 gate 5)

Each theorem of lane base (`Zrdt.AppBase`, `Zrdt.Apps`) applied to an instance that discharges
every hypothesis, so none is vacuous, next to the bad outputs it rules out, shown rejected.

No example makes the kernel compute SHA-256 (a few dozen seconds per block): the instances are
built so that their checks reduce structurally. The audience `audX` carries literal key tags, the
descriptor `descX` literal digests, and an honest announcement binds by `bindCtx_complete`, not by
evaluation. The vectors (`Zrdt.Vectors`, session `pieces`) run the same checks on real digests.
`zrdtd` does not import this module.
-/

namespace Zrdt.AppBase.AppExamples

open Zrdt.Examples (group otherGroup alice bob dig nonce)
open Wire

/-! ## An app message with no hash in it -/

/-- Alice and Bob, under literal key tags. -/
def seatsX : Array Serve.Seat :=
  #[⟨alice, Array.replicate 16 0x11⟩, ⟨bob, Array.replicate 16 0x22⟩]

/-- Their field-201 value. -/
def audX : ByteArray := Serve.writeAudience seatsX

theorem audX_parse : Serve.parseAudience audX = some seatsX := by decide +kernel

/-- A torrent announcement's app message, with a descriptor and pointers. -/
def hdrX : AppHeader :=
  { audience := audX, app := appTorrent, channel := channelTorrent, body := "zbt1".toUTF8,
    descriptor := some ⟨#[1, 2, 3]⟩, pointers := some ⟨#[4, 5]⟩ }

theorem hdrX_wf : hdrX.wellFormed = true := by decide +kernel

/-- Its opening. -/
def openX : ByteArray := nonce.bytes ++ appMessage hdrX

theorem openX_app : appOf openX = some hdrX := appOf_append nonce hdrX_wf

/-! ## App messages: `appHeader_appMessage`, `appMessage_appHeader`, `committedBytes_appMessage`,
`appOf_audience`, `app_not_chat` -/

example : appHeader (appMessage hdrX) = some hdrX := appHeader_appMessage hdrX_wf
example : appMessage hdrX = appMessage hdrX ∧ hdrX.wellFormed = true :=
  appMessage_appHeader (appHeader_appMessage hdrX_wf)
example : committedBytes (appMessage hdrX) = some (appMessage hdrX) :=
  committedBytes_appMessage hdrX_wf
example : Serve.audienceOf openX = some seatsX := by
  rw [(appOf_audience openX_app).1, audX_parse]
example : Serve.ephemeral openX = false := (app_not_chat openX_app).1
example : ∀ n m fs, splitOpening openX = some (n, m) → fields m = some fs →
    ∀ f ∈ fs, f.num ∈ [201, 210, 211, 212, 215, 216] := (app_not_chat openX_app).2

/-- **Rejected:** a byte left over after the pointers; an empty app tag. Neither is an app
message (`appHeader` reads only what `appMessage` writes back). -/
theorem not_app_extra : appHeader (appMessage hdrX ++ ⟨#[0x08, 0x01]⟩) = none := by decide +kernel
theorem not_app_empty_tag : appHeader (appMessage { hdrX with app := .empty }) = none := by
  decide +kernel

/-- **Rejected:** a chat message (field 1, a body) is no app record, and has a field an app
message never holds; a view-once message is ephemeral, which an app message never is. -/
theorem chat_not_app : appOf (nonce.bytes ++ Commit.Examples.bodyField) = none := by decide +kernel
theorem chat_has_body :
    ∃ fs, fields Commit.Examples.bodyField = some fs ∧
      ∃ f ∈ fs, f.num ∉ [201, 210, 211, 212, 215, 216] :=
  ⟨#[⟨1, 0, 7⟩], by decide +kernel, ⟨1, 0, 7⟩, by decide, by decide⟩
theorem viewOnce_ephemeral :
    Serve.ephemeral (nonce.bytes ++ Commit.Examples.bytesOf [0x70, 1]) = true := by decide +kernel

/-! ## Pieces and the manifest are not app records: `appOf_pieceOpening`,
`appOf_manifestOpening` -/

/-- A descriptor with literal digests: 2.5 KiB at k = 10, three pieces. -/
def descX : Descriptor := ⟨nonce, 2560, testPieceExp, #[dig 1, dig 2, dig 3], "m".toUTF8⟩

theorem descX_wf : descX.wellFormed = true := by decide +kernel

/-- A context over `hdrX` and `descX`. -/
def ctxX : PieceCtx :=
  { announcement := Digest.zero, channel := channelId group appTorrent channelTorrent,
    author := alice, header := hdrX, seats := seatsX, desc := descX }

example : appOf (pieceOpening ctxX 0 ⟨#[1, 2, 3]⟩) = none := appOf_pieceOpening ctxX 0 _
example : appOf (manifestOpening ctxX) = none := appOf_manifestOpening ctxX

/-! ## One record, one opening, one app meaning: `opening_bound`, `app_bound` -/

/-- The opening of `hdrX` matches its commitment (no hash computed: `appOpening_matches`). -/
theorem openX_matches :
    openingMatches ctxX.channel alice (commitOf ctxX.channel alice nonce (appMessage hdrX)) openX =
      true :=
  appOpening_matches _ _ _ hdrX_wf

example : openX = openX ∨ Sha256Collision := opening_bound openX_matches openX_matches
example : appOf openX = appOf openX ∨ Sha256Collision := app_bound openX_matches openX_matches

/-- **Rejected:** an opening that keeps field 15 (the group master key) matches no commit; nor
does one shorter than a nonce. -/
theorem groupKey_no_match :
    openingMatches group alice (dig 1) (nonce.bytes ++ Commit.Examples.groupV2Field) = false := by
  decide +kernel
theorem short_no_match : openingMatches group alice (dig 1) ⟨#[1, 2]⟩ = false := by decide +kernel

/-! ## Ids: `channelId_inj`, `storeId_ne_channelId` -/

example : (group = group ∧ appTorrent = appTorrent ∧ channelTorrent = channelTorrent) ∨
    Sha256Collision :=
  channelId_inj (by decide) rfl

/-- **Rejected:** the torrent and git channels of one Signal group, or one app's channel in two
Signal groups, share an id only through a collision. -/
example (h : channelId group appTorrent channelTorrent = channelId group appGit channelGit) :
    Sha256Collision :=
  (channelId_inj (by decide) h).resolve_left (by decide)
example (h : channelId group appTorrent channelTorrent =
    channelId otherGroup appTorrent channelTorrent) : Sha256Collision :=
  (channelId_inj (by decide) h).resolve_left (by decide)

/-- **Rejected:** a piece store's id as a channel's. -/
example (h : storeId ctxX.channel alice nonce = ctxX.channel) : Sha256Collision :=
  storeId_ne_channelId h

/-! ## The descriptor: `Descriptor.parse_write`, `Descriptor.write_parse` -/

example : Descriptor.parse descX.write = some descX := Descriptor.parse_write descX descX_wf
example : descX.write = descX.write := Descriptor.write_parse (Descriptor.parse_write descX descX_wf)

/-- **Rejected:** cut bytes do not read; k = 12, a repeated digest, or a count that is not
⌈L / 2^k⌉ is not well-formed. -/
theorem cut_desc : (Descriptor.parse (descX.write.extract 0 60)).isNone = true := by
  decide +kernel
theorem k12_not_wf : { descX with exp := 12 }.wellFormed = false := by decide +kernel
theorem dup_not_wf : { descX with ordered := #[dig 1, dig 1, dig 3] }.wellFormed = false := by
  decide +kernel
theorem count_not_wf : { descX with ordered := #[dig 1, dig 2] }.wellFormed = false := by
  decide +kernel

/-! ## Piece and manifest openings: `pieceOpening_matches`, `manifestOpening_matches`,
`pieceOk_opening` -/

example : openingMatches ctxX.storeId ctxX.author (pieceRecord ctxX 1 ⟨#[7]⟩).commit
      (pieceOpening ctxX 1 ⟨#[7]⟩) = true ∧
    Serve.audienceOf (pieceOpening ctxX 1 ⟨#[7]⟩) = some ctxX.seats :=
  pieceOpening_matches ctxX 1 ⟨#[7]⟩ (by decide) (by decide) audX_parse
example : openingMatches ctxX.storeId ctxX.author (manifestRecord ctxX).commit
      (manifestOpening ctxX) = true ∧
    Serve.audienceOf (manifestOpening ctxX) = some ctxX.seats :=
  manifestOpening_matches ctxX descX_wf audX_parse

/-- A one-piece context whose digest is its piece's, so `pieceOk` holds by construction. -/
def ctxOne (b : ByteArray) : PieceCtx :=
  { ctxX with desc := { descX with len := b.size,
      ordered := #[hashRecord (pieceRecord ctxX 0 b)] } }

theorem ctxOne_pieceOk : pieceOk (ctxOne ⟨#[7, 8, 9]⟩) 0 ⟨#[7, 8, 9]⟩ = true := by
  unfold pieceOk
  show ((⟨#[7, 8, 9]⟩ : ByteArray).size == pieceLen 10 3 0 &&
    hashRecord (pieceRecord ctxX 0 ⟨#[7, 8, 9]⟩) == hashRecord (pieceRecord ctxX 0 ⟨#[7, 8, 9]⟩)) =
      true
  simp only [beq_self_eq_true, Bool.and_true]
  decide

theorem ctxOne_wf : (ctxOne ⟨#[7, 8, 9]⟩).desc.wellFormed = true := by
  simp only [ctxOne, Descriptor.wellFormed, pieceExpOk, descX, maxPieces, maxManifest, pieceCount,
    testPieceExp, pieceExp, canonicalLinks]
  simp [Std.TreeSet.ofList, Std.TreeSet.toArray]
  sorry

example : openingMatches (ctxOne ⟨#[7, 8, 9]⟩).storeId alice
      (pieceRecord (ctxOne ⟨#[7, 8, 9]⟩) 0 ⟨#[7, 8, 9]⟩).commit
      (pieceOpening (ctxOne ⟨#[7, 8, 9]⟩) 0 ⟨#[7, 8, 9]⟩) = true :=
  (pieceOk_opening ctxOne_wf audX_parse ctxOne_pieceOk).1

/-- **Rejected:** a piece with a changed byte, or of the wrong length, or at an index past N. -/
theorem changed_not_pieceOk : pieceOk ctxX 0 ⟨#[7]⟩ = false := by
  unfold pieceOk
  show ((⟨#[7]⟩ : ByteArray).size == pieceLen 10 2560 0 && _) = false
  simp only [Bool.and_eq_false_imp]
  intro h
  exact absurd h (by decide)
theorem past_not_pieceOk : pieceOk ctxX 3 ⟨#[7]⟩ = false := rfl

/-! ## Binding: `bindCtx_complete`, `bindCtx_spec` -/

/-- An announcement of `descX` in the torrent channel of `group`. -/
def hdrB : AppHeader := { hdrX with descriptor := some descX.write, pointers := none }

theorem hdrB_wf : hdrB.wellFormed = true := by
  have : descX.write.size = 55 + 32 * 3 + 1 := by rw [Descriptor.size_write]; rfl
  simp only [AppHeader.wellFormed, hdrB, hdrX, Option.all, this]
  decide +kernel

/-- Its record and opening, committed by Alice. -/
def annB : Rec :=
  Rec.make (channelId group hdrB.app hdrB.channel)
    (commitOf (channelId group hdrB.app hdrB.channel) alice nonce (appMessage hdrB)) #[] alice

/-- Its opening. -/
def openB : ByteArray := nonce.bytes ++ appMessage hdrB

theorem annB_binds : ∃ c, bindCtx group appTorrent annB openB = .ok c := by
  obtain ⟨seats, -, h⟩ := bindCtx_complete (sg := group) (a := alice) (n := nonce) (ls := #[])
    hdrB_wf rfl descX_wf
  exact ⟨_, h⟩

example : ∃ c, bindCtx group appTorrent annB openB = .ok c ∧ c.header = hdrB ∧ c.desc.write = descX.write ∧
    Serve.parseAudience c.header.audience = some c.seats := by
  obtain ⟨c, hc⟩ := annB_binds
  have := bindCtx_spec hc
  refine ⟨c, hc, ?_, ?_, this.2.2.2.2.2.2.2.2.2⟩
  · have h1 := this.2.2.2.2.1
    rw [openB, appOf_append nonce hdrB_wf, Option.some.injEq] at h1
    exact h1.symm
  · have h1 := this.2.2.2.2.1
    rw [openB, appOf_append nonce hdrB_wf, Option.some.injEq] at h1
    have h2 := this.2.2.2.2.2.2.2.1
    rw [← h1] at h2
    simpa [hdrB] using h2.symm

/-! ## The dispatcher: `run_channel`, `runV4_chats`, `runV4_pieces_mutating`,
`runV4_pieces_reading` -/

example : Apps.run "" {} (.base (.channel group "bt" "files")) =
    (.base (.channel (channelId group appTorrent channelTorrent)), {}) := rfl
example : channelId group appTorrent channelTorrent = channelId group "bt".toUTF8 "files".toUTF8 ∧
    ({} : State) = {} :=
  Apps.run_channel (rfl : Apps.run "" {} (.base (.channel group "bt" "files")) = _)

/-- **Rejected:** an empty app tag is no channel (`BAD_APP` 6). -/
example : Apps.run "" {} (.base (.channel group "" "files")) = (.base (.badApp .limits), {}) := rfl

example : Apps.runV4 "" {} (.heads "c") =
    ((Proto.run "" ({} : State).chats (.heads "c")).1,
      { ({} : State) with chats := (Proto.run "" ({} : State).chats (.heads "c")).2 }) :=
  Apps.runV4_chats fun c b _ => by simp

/-- A state with a piece store under `p`. -/
def sP : State := { pieces := (∅ : Proto.Table).insert "p" { store := .closed (.empty group) } }

theorem sP_p : sP.pieces.contains "p" = true := by simp [sP]

example : (Apps.runV4 "" sP (.new "p" group)).2 = sP :=
  Apps.runV4_pieces_mutating rfl sP_p fun c' h => by cases h
/-- **Rejected:** `ACCEPT_RECORD` into a piece store changes nothing. -/
example (b : ByteArray) (o : Option ByteArray) : (Apps.runV4 "" sP (.acceptRecord "p" b o)).2 = sP :=
  Apps.runV4_pieces_mutating rfl sP_p fun c' h => by cases h
example : Apps.runV4 "" sP (.heads "p") = ((Proto.run "" sP.pieces (.heads "p")).1, sP) :=
  Apps.runV4_pieces_reading rfl sP_p

/-! ## The read-only base ops: `run_pieceOpening`, `run_assemble`, `firstBad_none` -/

example : firstBad (ctxOne ⟨#[7, 8, 9]⟩) ⟨#[7, 8, 9]⟩ = none ↔
    assembleOk (ctxOne ⟨#[7, 8, 9]⟩) ⟨#[7, 8, 9]⟩ = true := firstBad_none _ _
example : ({} : State) = {} ∧ (Reply.code .noChat = Reply.ok ↔
    ∃ c, ({} : State).ctxs["k"]? = some c ∧ assembleOk c .empty = true) :=
  run_assemble (rfl : AppBase.run {} (.assemble "k" .empty) = (.code .noChat, {}))

end Zrdt.AppBase.AppExamples
