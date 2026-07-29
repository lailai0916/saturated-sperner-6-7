import AiMathLab.P0054MiddleSevenNineExtension
import AiMathLab.P0054MiddleSevenEightFanoBranch

/-!
# The non-`K₄` branch of a three-row on the nine-row side

If a three-point blocker row covers the seven-row family, one of its points
has degree three.  The four avoiding rows are classified by the exact
136-vector certificate.  Kernel blocker cardinalities eight and nine are
then ruled out by the checked extension model.  The remaining cardinality
seven is the unique `K₄` branch and is isolated for a separate argument.
-/

namespace AiMathLab.P0054.MiddleSevenNineNineSide

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFanoBranch
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.MiddleSevenNineDegree
open AiMathLab.P0054.MiddleSevenNineExtension
open AiMathLab.P0054.MiddleSevenNineFinite

theorem fourKernel_values_eq_k4_of_blocker_card_seven {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {K : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ K)
    (hKClutter : IsClutter K)
    (hBKRows : RowsCardAtLeast (blocker K) 2)
    (hKRows : RowsCardAtLeast K 3)
    (hKUpper : ∀ E ∈ K, E.card ≤ 9)
    (hBKCard : (blocker K).card = 7)
    (hPairCard : (pairRows (blocker K)).card ≤ 4) :
    (fourActualSupportMultiplicity rowOrder).toList = sevenEightK4Values := by
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hKClutter hBKRows hKRows hKUpper (by omega) hPairCard
  have hProfile := middleFourActualSupportMultiplicity_profile rowOrder
    hKClutter hBKRows hKRows hKUpper (by omega) hPairCard
  have hWeighted := fourWeightedCoverCount_le_blocker_card rowOrder hBKRows
  have hSeven :
      fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) = 7 ∧
        fourPairCoverCount (fourActualSupportMultiplicity rowOrder) = 3 := by
    rcases hProfile with hSeven | hEight | hNineThree | hNineFour
    · exact hSeven
    · rw [hBKCard] at hWeighted
      omega
    · rw [hBKCard] at hWeighted
      omega
    · rw [hBKCard] at hWeighted
      omega
  unfold MiddleSevenNineFinite.middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  have hArray : values.toArray = fourActualSupportMultiplicity rowOrder := by
    rw [← hList]
  exact hList.trans (middleFourMultiplicityCertificate_k4_of_seven
    values hValues (by simpa [hArray] using hSeven.1)
      (by simpa [hArray] using hSeven.2))

theorem threeRow_on_nineSide_nonK4_impossible {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBCard : (blocker H).card = 9)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 4)
    {T : G413.Row alpha} (hT : T ∈ blocker H) (hTCard : T.card = 3)
    (hKernelNotSeven : ∀ x ∈ T, degree H x = 3 →
      (blocker (avoidPoint H x)).card ≠ 7) : False := by
  classical
  obtain ⟨x, hxT, hDegree⟩ :=
    exists_degree_three_mem_three_blocker_row_of_card_seven
      hT hTCard hHCard hHMaxDegree
  let K := avoidPoint H x
  have hKCard : K.card = 4 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro row hRow
    exact hHRows row (mem_avoidPoint.mp (by simpa [K] using hRow)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hKUpper : ∀ row ∈ K, row.card ≤ 9 := by
    intro row hRow
    have hRowH : row ∈ H :=
      (mem_avoidPoint.mp (by simpa [K] using hRow)).1
    have hRowDual : row ∈ blocker (blocker H) := by
      simpa [blocker_involution hHClutter] using hRowH
    exact (minimalTransversal_card_le_rows
      (mem_blocker.mp hRowDual)).trans_eq hBCard
  have hBKUpper : (blocker K).card ≤ 9 := by
    simpa [K, hBCard] using blocker_avoidPoint_card_le_blocker H x
  have hPairUpper : (pairRows (blocker K)).card ≤ 4 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 4 := hBMaxDegree x
  let rowOrder := fourRowOrder hKCard
  have hProfile := middleFourActualSupportMultiplicity_profile rowOrder
    hKClutter hBKRows hKRows hKUpper hBKUpper hPairUpper
  have hWeighted := fourWeightedCoverCount_le_blocker_card rowOrder hBKRows
  have hBKLower : 7 ≤ (blocker K).card := by
    rcases hProfile with hSeven | hEight | hNineThree | hNineFour
    · omega
    · omega
    · omega
    · omega
  have hBKNotSeven : (blocker K).card ≠ 7 := by
    simpa [K] using hKernelNotSeven x hxT hDegree
  have hLengthLeEight :=
    middleFourActualSupportMultiplicity_activePoints_length rowOrder
      hKClutter hBKRows hKRows hKUpper hBKUpper hPairUpper
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 := by omega
  have hSelectionBound := middleFourSemanticSelected_length_bound
    H x rowOrder hBRows hBKRows hLength (hBMaxDegree x)
  have hSelection : middleFourSemanticSelected H x rowOrder ∈
    middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList :=
    middleFourSemanticSelected_mem_liftSelectionRows
      H x rowOrder hSelectionBound
  have hCheck := sevenNineExtensionActualCheck rowOrder
    hKClutter hBKRows hKRows hKUpper hBKUpper hPairUpper
  interval_cases hBKCard : (blocker K).card
  · exact hBKNotSeven rfl
  · exact blocker_card_eight_contradicts_check x rowOrder
      hHClutter hHCard hBRows hBCard hBKRows hLengthLeEight
      (by simpa [K] using hBKCard) hBMaxDegree hSelection hCheck
  · exact blocker_card_nine_contradicts_check x rowOrder
      hHClutter hBRows hBKRows hLength
      (by simpa [K] using hBKCard) hBCard hHCard hBMaxDegree
      hSelection hCheck

theorem threeRow_on_nineSide_forces_k4_kernel {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBCard : (blocker H).card = 9)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 4)
    {T : G413.Row alpha} (hT : T ∈ blocker H) (hTCard : T.card = 3) :
    ∃ x ∈ T, degree H x = 3 ∧
      (blocker (avoidPoint H x)).card = 7 := by
  classical
  by_contra hNoK4
  have hKernelNotSeven : ∀ x ∈ T, degree H x = 3 →
      (blocker (avoidPoint H x)).card ≠ 7 := by
    intro x hxT hDegree hCard
    exact hNoK4 ⟨x, hxT, hDegree, hCard⟩
  exact threeRow_on_nineSide_nonK4_impossible
    hHClutter hHCard hHRows hHMaxDegree hBCard hBRows hBMaxDegree
      hT hTCard hKernelNotSeven

end AiMathLab.P0054.MiddleSevenNineNineSide
