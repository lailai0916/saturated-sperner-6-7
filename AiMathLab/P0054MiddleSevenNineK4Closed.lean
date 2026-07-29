import AiMathLab.P0054MiddleSevenNineK4Certificate
import AiMathLab.P0054MiddleSevenNineK4

/-!
# Closed `K₄` branch of the seven-plus-nine split
-/

namespace AiMathLab.P0054.MiddleSevenNineK4

open AiMathLab.P0054.G413
open AiMathLab.P0054.MiddleSevenNineK4Finite

theorem threeRow_on_nineSide_impossible {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBlockerCard : (blocker H).card = 9)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBlockerMaxDegree : MaxDegreeAtMost (blocker H) 4)
    {T : G413.Row alpha} (hT : T ∈ blocker H) (hTCard : T.card = 3) :
    False :=
  threeRow_on_nineSide_impossible_of_check hHClutter hHCard hHRows
    hHMaxDegree hBlockerCard hHBlockerRows hBlockerMaxDegree hT hTCard
      sevenNineK4ExtensionCheck_true

end AiMathLab.P0054.MiddleSevenNineK4
