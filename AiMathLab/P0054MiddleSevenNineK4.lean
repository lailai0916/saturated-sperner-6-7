import AiMathLab.P0054MiddleSevenNineK4SoundCore
import AiMathLab.P0054MiddleSevenNineNineSide

/-!
# Exclusion of the `K₄` kernel in the seven-plus-nine split

The finite two-extra-row certificate is connected here to the four-row
kernel selected by the semantic reduction.  The certificate itself is an
explicit theorem parameter so that its chunks can be compiled separately.
-/

namespace AiMathLab.P0054.MiddleSevenNineK4

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.MiddleSevenNineDegree
open AiMathLab.P0054.MiddleSevenNineK4Finite
open AiMathLab.P0054.MiddleSevenNineK4Sound
open AiMathLab.P0054.MiddleSevenNineNineSide

theorem k4_kernel_impossible_of_check {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBlockerCard : (blocker H).card = 9)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBlockerMaxDegree : MaxDegreeAtMost (blocker H) 4)
    {x : alpha} (hDegree : degree H x = 3)
    (hAvoidBlockerCard : (blocker (avoidPoint H x)).card = 7)
    (hCheck : sevenNineK4ExtensionCheck = true) : False := by
  let K := avoidPoint H x
  have hKCard : K.card = 4 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro row hRow
    exact hHRows row
      (mem_avoidPoint.mp (by simpa [K] using hRow)).1
  have hAvoidBlockerRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using
      blocker_avoidPoint_rows_cardAtLeast_two hHBlockerRows x
  have hKUpper : ∀ row ∈ K, row.card ≤ 9 := by
    intro row hRow
    have hRowH : row ∈ H :=
      (mem_avoidPoint.mp (by simpa [K] using hRow)).1
    have hRowDouble : row ∈ blocker (blocker H) := by
      simpa [blocker_involution hHClutter] using hRowH
    exact (minimalTransversal_card_le_rows
      (mem_blocker.mp hRowDouble)).trans_eq hBlockerCard
  have hPairUpper : (pairRows (blocker K)).card ≤ 4 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using
          pairRows_blocker_avoidPoint_card_le_degree hHBlockerRows x
      _ ≤ 4 := hBlockerMaxDegree x
  let rowOrder := fourRowOrder hKCard
  have hValuesK4 :
      (fourActualSupportMultiplicity rowOrder).toList =
        sevenEightK4Values :=
    fourKernel_values_eq_k4_of_blocker_card_seven rowOrder
      hKClutter hAvoidBlockerRows hKRows hKUpper
        (by simpa [K] using hAvoidBlockerCard) hPairUpper
  have hValues :
      (fourActualSupportMultiplicity rowOrder).toList =
        middleFourDegreeFourVector20 :=
    hValuesK4.trans sevenEight_k4_eq_vector20
  have hLengthEq := sevenNineK4_activePoints_length_eq_six
    rowOrder hValues
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  have hSelectionBound := middleFourSemanticSelected_length_bound
    H x rowOrder hHBlockerRows hAvoidBlockerRows hLength
      (hBlockerMaxDegree x)
  have hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList :=
    middleFourSemanticSelected_mem_liftSelectionRows
      H x rowOrder hSelectionBound
  exact sevenNineK4_contradicts_check H x rowOrder hHClutter hHCard
    hHRows hHMaxDegree hBlockerCard hHBlockerRows hBlockerMaxDegree
      hDegree (by simpa [K] using hAvoidBlockerCard)
        hAvoidBlockerRows hValues hSelection hCheck

theorem threeRow_on_nineSide_impossible_of_check {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBlockerCard : (blocker H).card = 9)
    (hHBlockerRows : RowsCardAtLeast (blocker H) 3)
    (hBlockerMaxDegree : MaxDegreeAtMost (blocker H) 4)
    {T : G413.Row alpha} (hT : T ∈ blocker H) (hTCard : T.card = 3)
    (hCheck : sevenNineK4ExtensionCheck = true) : False := by
  obtain ⟨x, _hxT, hDegree, hAvoidBlockerCard⟩ :=
    threeRow_on_nineSide_forces_k4_kernel hHClutter hHCard hHRows
      hHMaxDegree hBlockerCard hHBlockerRows hBlockerMaxDegree
        hT hTCard
  exact k4_kernel_impossible_of_check hHClutter hHCard hHRows
    hHMaxDegree hBlockerCard hHBlockerRows hBlockerMaxDegree
      hDegree hAvoidBlockerCard hCheck

end AiMathLab.P0054.MiddleSevenNineK4
