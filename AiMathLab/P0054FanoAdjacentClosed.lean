import AiMathLab.P0054AdjacentFourIntersecting
import AiMathLab.P0054FanoAdjacentNearlyClosed

/-!
# The closed Fano-adjacent exclusion

The arbitrary-ground four-row intersecting theorem discharges the final
parameter in the Fano-adjacent reduction.
-/

namespace AiMathLab.P0054.FanoAdjacentClosed

open AiMathLab.P0054.G413
open AiMathLab.P0054.FanoAdjacentBridge
open AiMathLab.P0054.FanoAdjacentNearlyClosed

theorem fano_adjacent_impossible
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha] :
    FanoAdjacentImpossiblePrinciple alpha :=
  fano_adjacent_impossible_of_four_bound (by
    intro H hClutter hCard hRows hBlockerRows hPairwise
    exact
      AiMathLab.P0054.AdjacentFourIntersecting.four_pairwise_intersecting_blocker_card_ge_ten
        hClutter hCard hRows hPairwise hBlockerRows)

end AiMathLab.P0054.FanoAdjacentClosed
