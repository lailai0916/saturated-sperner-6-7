import AiMathLab.P0054G419.KernelAActualWitness
import AiMathLab.P0054G419.KernelAClassificationChecks
import AiMathLab.P0054G419.KernelAExclusionChecks

namespace AiMathLab.P0054.G419

open G413

theorem fourActualSupportMultiplicity_in_certificate {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 6)
    (hThree : ∃ E ∈ T, E.card = 3)
    (hBCard : (blocker T).card ≤ 6) :
    fourMultiplicityInCertificate
      (fourActualSupportMultiplicity rowOrder) = true := by
  have hCheck := List.all_eq_true.mp four_kernel_a_classification_check
    (fourMultiplicityMask (fourActualSupportMultiplicity rowOrder))
    (List.mem_range.mpr
      (fourMultiplicityMask_lt (fourActualSupportMultiplicity rowOrder)))
  exact fourActualSupportMultiplicity_in_certificate_of_check rowOrder
    hTClutter hBRows hTRows hTUpper hThree hBCard hCheck

set_option maxRecDepth 1000000 in
theorem fourMultiplicityCertificate_weightedCoverCount_ge_five :
    ∀ values ∈ fourMultiplicityCertificate,
      5 ≤ fourWeightedCoverCount values.toArray := by
  decide

theorem fourActualSupportMultiplicity_weightedCoverCount_ge_five {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 6)
    (hThree : ∃ E ∈ T, E.card = 3)
    (hBCard : (blocker T).card ≤ 6) :
    5 ≤ fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) := by
  have hCertificate := fourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hThree hBCard
  unfold fourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  have hArray : values.toArray = fourActualSupportMultiplicity rowOrder := by
    rw [← hList]
  rw [← hArray]
  exact fourMultiplicityCertificate_weightedCoverCount_ge_five values hValues

theorem fourActualSupportMultiplicity_exact_incompatible {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 6)
    (hThree : ∃ E ∈ T, E.card = 3)
    (hBCard : (blocker T).card ≤ 6) :
    fourKernelCompatibleExact (fourActualSupportMultiplicity rowOrder) = false := by
  have hCertificate := fourActualSupportMultiplicity_in_certificate rowOrder
    hTClutter hBRows hTRows hTUpper hThree hBCard
  unfold fourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  have hArray : values.toArray = fourActualSupportMultiplicity rowOrder := by
    rw [← hList]
  have hIncompatible := four_kernel_a_certificate_incompatible hValues
  rwa [hArray] at hIncompatible

theorem fourKernelA_actual_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 6)
    (hThree : ∃ E ∈ T, E.card = 3)
    (hBCard : (blocker T).card ≤ 6)
    (hCompatible :
      fourKernelCompatibleExact (fourActualSupportMultiplicity rowOrder) = true) :
    False := by
  have hIncompatible := fourActualSupportMultiplicity_exact_incompatible rowOrder
    hTClutter hBRows hTRows hTUpper hThree hBCard
  rw [hCompatible] at hIncompatible
  exact Bool.noConfusion hIncompatible

end AiMathLab.P0054.G419
