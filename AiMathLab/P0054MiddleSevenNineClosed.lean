import AiMathLab.P0054MiddleSevenNineBridge
import AiMathLab.P0054MiddleSevenNineFiveKernelClosed
import AiMathLab.P0054MiddleSevenNineSixCouplingClosed

/-!
# Closing the seven-plus-nine middle split

The two arbitrary-finite principles required by the aggregation bridge are
supplied by the analytic five-row argument and the checked six-row residual
coupling certificate.
-/

namespace AiMathLab.P0054.MiddleSevenNineClosed

open AiMathLab.P0054.G413

theorem sevenNine_impossible
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 9) : False := by
  exact
    AiMathLab.P0054.MiddleSevenNineBridge.sevenNine_impossible_of_principles
      AiMathLab.P0054.MiddleSevenNineFiveKernelClosed.fiveRowRowsFourImpossiblePrinciple
      AiMathLab.P0054.MiddleSevenNineSixCouplingClosed.sixRowLowDegreeImpossiblePrinciple
      hHClutter hHCard hHRows hBRows hBCard

end AiMathLab.P0054.MiddleSevenNineClosed
