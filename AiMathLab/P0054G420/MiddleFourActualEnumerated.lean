import AiMathLab.P0054G420.MiddleFourClassificationChecks
import AiMathLab.P0054G420.MiddleFourCertificate

namespace AiMathLab.P0054.G420

open G413 G419

theorem middleFourActualSupportMultiplicity_in_certificate {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 8)
    (hBCard : (blocker T).card ≤ 8)
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
    (hTUpper : ∀ E ∈ T, E.card ≤ 8)
    (hBCard : (blocker T).card ≤ 8)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    let actual := fourActualSupportMultiplicity rowOrder
    (fourWeightedCoverCount actual = 8 ∧ fourPairCoverCount actual = 4) ∨
      (fourWeightedCoverCount actual = 7 ∧ fourPairCoverCount actual = 3) := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : actual.toList = values := of_decide_eq_true hListCheck
  have hArray : values.toArray = actual := by
    rw [← hList]
  simpa [hArray] using middleFourMultiplicityCertificate_profile values hValues

theorem middleFourActualSupportMultiplicity_canonical {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {T : G413.Hypergraph alpha} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 8)
    (hBCard : (blocker T).card ≤ 8)
    (hPairCard : (pairRows (blocker T)).card ≤ 4) :
    let actual := fourActualSupportMultiplicity rowOrder
    middleFourCanonicalRepresentatives.any fun representative ↦
      fourRowPermutationEquivalent actual.toList representative := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hBCard hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : actual.toList = values := of_decide_eq_true hListCheck
  change middleFourCanonicalRepresentatives.any (fun representative ↦
    fourRowPermutationEquivalent actual.toList representative) = true
  rw [hList]
  exact middleFourMultiplicityCertificate_canonical values hValues

end AiMathLab.P0054.G420
