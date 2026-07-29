import AiMathLab.P0054FanoAdjacentEightFiveFinite
import AiMathLab.P0054FanoAdjacentSevenSixSound

/-!
# Soundness of the finite Fano eight-plus-five core certificate
-/

namespace AiMathLab.P0054.FanoAdjacentEightFiveSound

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.FanoAdjacentSevenSixFinite
open AiMathLab.P0054.FanoAdjacentEightFiveFinite

theorem fanoEightFiveCoreSelectionCheck_sound
    {rows : List (G413.Row MiddleFourModelPoint)}
    {extra : G413.Row MiddleFourModelPoint}
    (hRows : rows ∈ fanoSevenSixSelections)
    (hExtra : extra ∈ fanoEightFiveCoreExtras)
    (hExtraCardLower : 2 ≤ extra.card)
    (hExtraCardUpper : extra.card ≤ 5)
    (hClutter : IsClutter (insert extra rows.toFinset))
    (hDualRows : RowsCardAtLeast
      (blocker (insert extra rows.toFinset)) 4) :
    6 ≤ (blocker (insert extra rows.toFinset)).card := by
  have hRowsChecked := List.all_eq_true.mp
    fanoEightFiveCore_check rows hRows
  unfold fanoEightFiveCoreSelectionCheck at hRowsChecked
  dsimp only at hRowsChecked
  have hExtraChecked := List.all_eq_true.mp hRowsChecked extra hExtra
  have hValid : fanoEightFiveCoreExtraValid rows extra = true :=
    fanoEightFiveCoreExtraValid_eq_true_of_clutter rows extra
      hExtraCardLower hExtraCardUpper hClutter
  have hStep :
      finiteFastBlockerStep (finiteFastBlocker rows) extra =
        blocker (insert extra rows.toFinset) :=
    calc
      finiteFastBlockerStep (finiteFastBlocker rows) extra =
          fastBlockerStep (fastBlocker rows) extra := by
        rw [finiteFastBlocker_eq_fastBlocker,
          finiteFastBlockerStep_eq_fastBlockerStep]
      _ = blocker (insert extra rows.toFinset) :=
        fastBlockerStep_eq_blocker_insert rows.toFinset
          (fastBlocker rows) extra (fastBlocker_eq_blocker rows)
  have hStepRows : RowsCardAtLeast
      (finiteFastBlockerStep (finiteFastBlocker rows) extra) 4 := by
    rw [hStep]
    exact hDualRows
  have hRowsBool : modelRowsCardAtLeast
      (finiteFastBlockerStep (finiteFastBlocker rows) extra) 4 = true :=
    (modelRowsCardAtLeast_eq_true_iff _ _).2 hStepRows
  change (!fanoEightFiveCoreExtraValid rows extra ||
      (!modelRowsCardAtLeast
          (finiteFastBlockerStep (finiteFastBlocker rows) extra) 4 ||
        decide (6 ≤
          (finiteFastBlockerStep (finiteFastBlocker rows) extra).card))) = true
    at hExtraChecked
  rw [hValid, hRowsBool] at hExtraChecked
  have hCardBool : decide
      (6 ≤ (finiteFastBlockerStep
        (finiteFastBlocker rows) extra).card) = true := by
    simpa using hExtraChecked
  have hCard : 6 ≤
      (finiteFastBlockerStep (finiteFastBlocker rows) extra).card :=
    of_decide_eq_true hCardBool
  rwa [hStep] at hCard

end AiMathLab.P0054.FanoAdjacentEightFiveSound
