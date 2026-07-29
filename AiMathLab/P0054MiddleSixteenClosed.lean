import AiMathLab.P0054MiddleSixteenBridge
import AiMathLab.P0054MiddleSevenNineClosed

/-!
# Closing middle total sixteen

All oriented cardinal splits are discharged by the general bridge after the
seven-plus-nine endpoint is instantiated with its concrete proof.
-/

namespace AiMathLab.P0054.MiddleSixteenClosed

open AiMathLab.P0054.G413

theorem middle_sixteen_impossible
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hTotal : H.card + (blocker H).card = 16)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) : False := by
  exact
    AiMathLab.P0054.MiddleSixteenBridge.middle_sixteen_impossible_of_seven_nine
      AiMathLab.P0054.MiddleSevenNineClosed.sevenNine_impossible
      hHClutter hTotal hHRows hBRows

end AiMathLab.P0054.MiddleSixteenClosed
