import AiMathLab.P0054MiddleFourteen
import AiMathLab.P0054MiddleSevenSevenFano

/-!
# Classification at middle total fourteen

The cardinal split is seven plus seven, and the equality case is the Fano
clutter on its active points.
-/

namespace AiMathLab.P0054.MiddleFourteenFano

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFinite

theorem middle_fourteen_is_fano {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hTotal : H.card + (blocker H).card = 14)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    H.card = 7 ∧ (blocker H).card = 7 ∧
      H = blocker H ∧
      (∀ E ∈ H, E.card = 3) ∧
      (∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).card = 1) ∧
      ∃ pointMap : alpha → MiddleFourModelPoint,
        Set.InjOn pointMap (H.biUnion id) ∧
        sevenEightFanoBase =
          H.image (fun row ↦ row.image pointMap) := by
  obtain ⟨hHCard, hBCard⟩ :=
    AiMathLab.P0054.MiddleFourteen.middle_fourteen_cards_eq_seven
      hHClutter hTotal hHRows hBRows
  obtain ⟨hSelf, hRows, hPairs, hModel⟩ :=
    AiMathLab.P0054.MiddleSevenSevenFano.sevenSeven_is_fano
      hHClutter hHCard hHRows hBRows hBCard
  exact ⟨hHCard, hBCard, hSelf, hRows, hPairs, hModel⟩

end AiMathLab.P0054.MiddleFourteenFano
