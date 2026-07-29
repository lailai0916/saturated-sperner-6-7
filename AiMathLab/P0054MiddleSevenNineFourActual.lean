import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationChecks
import AiMathLab.P0054MiddleSevenNineFourCertificate
import AiMathLab.P0054G420.MiddleFourDegreeFourBridge

/-!
# Semantic completeness of the seven-plus-nine four-row enumeration

This is the bridge from an arbitrary finite four-row clutter to the checked
136-vector certificate.  Parallel actual points are retained as exact support
multiplicities; no bound is imposed on the ambient ground set.
-/

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G413 G419 G420

theorem middleFourActualSupportMultiplicity_in_certificate {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9)
    (hBCard : (blocker T).card ≤ 9)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    middleFourMultiplicityInCertificate
      (fourActualSupportMultiplicity rowOrder) = true := by
  obtain ⟨hMask, finalDegrees, hGenerated⟩ :=
    middleFourActualSupportMultiplicity_enumeration_data rowOrder hTClutter
      hBRows hTRows hTUpper hBCard hPairCard
  have hCheck := List.all_eq_true.mp middle_four_classification_check
    (fourMultiplicityMask (fourActualSupportMultiplicity rowOrder))
    (List.mem_range.mpr
      (fourMultiplicityMask_lt (fourActualSupportMultiplicity rowOrder)))
  exact middleFourClassificationMaskCheck_sound hMask hGenerated
    (middleFourActualSupportMultiplicity_leaf_valid rowOrder
      hBRows hTRows hTUpper) hCheck

theorem middleFourActualSupportMultiplicity_profile {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9)
    (hBCard : (blocker T).card ≤ 9)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    let actual := fourActualSupportMultiplicity rowOrder
    (fourWeightedCoverCount actual = 7 ∧ fourPairCoverCount actual = 3) ∨
    (fourWeightedCoverCount actual = 8 ∧ fourPairCoverCount actual = 4) ∨
    (fourWeightedCoverCount actual = 9 ∧ fourPairCoverCount actual = 3) ∨
    (fourWeightedCoverCount actual = 9 ∧ fourPairCoverCount actual = 4) := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : actual.toList = values := of_decide_eq_true hListCheck
  have hArray : values.toArray = actual := by rw [← hList]
  simpa [hArray] using middleFourMultiplicityCertificate_profile values hValues

theorem middleFourActualSupportMultiplicity_canonical {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9)
    (hBCard : (blocker T).card ≤ 9)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    let actual := fourActualSupportMultiplicity rowOrder
    middleSevenNineFourCanonicalRepresentatives.any fun representative ↦
      fourRowPermutationEquivalent actual.toList representative := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : actual.toList = values := of_decide_eq_true hListCheck
  change middleSevenNineFourCanonicalRepresentatives.any (fun representative ↦
    fourRowPermutationEquivalent actual.toList representative) = true
  rw [hList]
  exact middleFourMultiplicityCertificate_canonical values hValues

theorem middleFourActualSupportMultiplicity_eq_k4_of_profile
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9)
    (hBCard : (blocker T).card ≤ 9)
    (hPairCard : (pairRows (blocker T)).card ≤ 4)
    (hWeighted : fourWeightedCoverCount
      (fourActualSupportMultiplicity rowOrder) = 7)
    (hPair : fourPairCoverCount
      (fourActualSupportMultiplicity rowOrder) = 3) :
    (fourActualSupportMultiplicity rowOrder).toList =
      MiddleSevenEightFinite.sevenEightK4Values := by
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  have hArray : values.toArray = fourActualSupportMultiplicity rowOrder := by
    rw [← hList]
  exact hList.trans (middleFourMultiplicityCertificate_k4_of_seven
    values hValues (by simpa [hArray] using hWeighted)
      (by simpa [hArray] using hPair))

theorem middleFourActualSupportMultiplicity_eq_k4_of_blocker_card_seven
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9)
    (hBCard : (blocker T).card = 7)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    (fourActualSupportMultiplicity rowOrder).toList =
      MiddleSevenEightFinite.sevenEightK4Values := by
  have hProfile := middleFourActualSupportMultiplicity_profile rowOrder
    hTClutter hBRows hTRows hTUpper (by omega) hPairCard
  have hWeightedUpper :=
    fourWeightedCoverCount_le_blocker_card rowOrder hBRows
  have hSeven :
      fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) = 7 ∧
        fourPairCoverCount (fourActualSupportMultiplicity rowOrder) = 3 := by
    rcases hProfile with hSeven | hEight | hNineThree | hNineFour
    · exact hSeven
    · rw [hBCard] at hWeightedUpper
      omega
    · rw [hBCard] at hWeightedUpper
      omega
    · rw [hBCard] at hWeightedUpper
      omega
  exact middleFourActualSupportMultiplicity_eq_k4_of_profile rowOrder
    hTClutter hBRows hTRows hTUpper (by omega) hPairCard
      hSeven.1 hSeven.2

theorem middleFourActualSupportMultiplicity_activePoints_length
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 9)
    (hBCard : (blocker T).card ≤ 9)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    (fourActivePoints (fourActualSupportMultiplicity rowOrder)).length ≤ 8 := by
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  have hLength := middleFourMultiplicityCertificate_supports_length values hValues
  rw [← hList, middleFourModelSupports_length_eq_activePoints] at hLength
  exact hLength

end AiMathLab.P0054.MiddleSevenNineFinite
