import Zrdt.Apps

/-!
# Piece stores: what they guarantee (docs/apps/BUILD_M1.md §C.2)

**Owner: lane torrent.** The piece-store theorems, about lane base's definitions and ops
(`Zrdt.AppBase`, the dispatcher `Zrdt.Apps`), without Mathlib: `pieceOk_unique`,
`bindCtx_unique`, `assemble_unique` (on `AppBase`'s reference definitions, provable now), and,
once lane base's ops exist, `run_piece_accept`, `run_complete`, `PiecesInv`, `run_piecesInv`,
`pieces_follow_announcement`, `serve_pieces`. They guard both apps' bulk data. `zrdtd` does not
import this module, so it is not part of `Apps.sources`.

Empty in the skeleton.
-/

namespace Zrdt.PieceProofs

open AppBase

end Zrdt.PieceProofs
