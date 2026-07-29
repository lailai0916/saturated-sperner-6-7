import AiMathLab.P0054FanoAdjacentEightFiveActual
import AiMathLab.P0054FanoAdjacentSevenSixActual

/-!
# Closing the Fano-adjacent principle from the four-row intersecting bound

All Fano-specific finite branches are discharged here.  The only parameter
left in this module is the arbitrary-finite theorem that four pairwise
intersecting rows of size at least four have at least ten minimal
transversals when all minimal transversals have size at least two.
-/

namespace AiMathLab.P0054.FanoAdjacentNearlyClosed

open AiMathLab.P0054.G413
open AiMathLab.P0054.FanoAdjacentBridge
open AiMathLab.P0054.FanoAdjacentBasics
open AiMathLab.P0054.FanoAdjacentSevenSixActual
open AiMathLab.P0054.FanoAdjacentEightFiveActual

def FourPairwiseIntersectingBoundPrinciple (alpha : Type*)
    [Fintype alpha] [DecidableEq alpha] : Prop :=
  ∀ {H : G413.Hypergraph alpha},
    IsClutter H →
    H.card = 4 →
    RowsCardAtLeast H 4 →
    RowsCardAtLeast (blocker H) 2 →
    (∀ first ∈ H, ∀ second ∈ H, first ≠ second →
      (first ∩ second).Nonempty) →
    10 ≤ (blocker H).card

theorem fano_adjacent_impossible_of_four_bound
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (hFourBound : FourPairwiseIntersectingBoundPrinciple alpha) :
    FanoAdjacentImpossiblePrinciple alpha := by
  intro middle small large pointMap hMiddleCard hMiddleRows hMiddlePairs
    hPointMap hModel hSmallBlocker hLargeBlocker hSmallRows hLargeRows
    hPred hSucc hTotal
  have hLargePairs : ∀ first ∈ large, ∀ second ∈ large,
      first ≠ second → (first ∩ second).Nonempty :=
    fano_successors_pairwise_intersecting
      hMiddleRows hMiddlePairs hSucc
  have hFour : large.card = 4 → 10 ≤ small.card := by
    intro hLargeCard
    have hLargeClutter : IsClutter large := by
      rw [hLargeBlocker]
      exact blocker_isClutter small
    have hDoubleRows : RowsCardAtLeast (blocker large) 2 := by
      rw [← hSmallBlocker]
      exact hSmallRows
    have hTen := hFourBound hLargeClutter hLargeCard hLargeRows
      hDoubleRows hLargePairs
    rwa [← hSmallBlocker] at hTen
  have hSeven : small.card = 7 → 7 ≤ large.card := by
    intro hSmallCard
    exact fano_seven_side_forces_large_card_ge_seven
      hMiddleCard hMiddleRows hMiddlePairs hPointMap hModel hLargeBlocker
        hSmallRows hLargeRows hPred hSmallCard
  have hEight : small.card = 8 → 6 ≤ large.card := by
    intro hSmallCard
    rcases fano_adjacent_cardinal_splits hMiddleCard hMiddlePairs
        hSmallBlocker hLargeBlocker hSmallRows hLargeRows hPred hTotal with
      hEightFour | hNineFour | hSevenFive | hEightFive | hSevenSix
    · have hTen := hFour hEightFour.2
      omega
    · omega
    · omega
    · exact (fano_eight_five_impossible
        hMiddleCard hMiddleRows hMiddlePairs hPointMap hModel
          hSmallBlocker hLargeBlocker hSmallRows hLargeRows hPred
          hSmallCard hEightFive.2).elim
    · omega
  exact fano_adjacent_impossible_of_cardinal_bounds
    hMiddleCard hMiddlePairs hSmallBlocker hLargeBlocker hSmallRows
      hLargeRows hPred hTotal hSeven hEight hFour

end AiMathLab.P0054.FanoAdjacentNearlyClosed
