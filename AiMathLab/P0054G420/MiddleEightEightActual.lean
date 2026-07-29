import AiMathLab.P0054G420.FiveRowPairExactPrinciple

namespace AiMathLab.P0054.G420

open G413

theorem eightEight_impossible
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) :
    False := by
  exact eightEight_impossible_of_fiveRowPairExact
    (fiveRowPairExactPrinciple alpha)
    hHClutter hHCard hHRows hBRows hBCard

end AiMathLab.P0054.G420
