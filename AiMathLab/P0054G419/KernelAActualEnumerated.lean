import AiMathLab.P0054G419.KernelAActualGenerated
import AiMathLab.P0054G419.KernelACoverCompleteChecks

namespace AiMathLab.P0054.G419

open G413

theorem fourActualSupportMultiplicity_size {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) :
    (fourActualSupportMultiplicity rowOrder).size = 14 := by
  simp [fourActualSupportMultiplicity]

theorem fourActualSupportMultiplicity_row_upper {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTUpper : ∀ E ∈ T, E.card ≤ 6) :
    ∀ row < 4,
      fourRowDegree (fourActualSupportMultiplicity rowOrder) row ≤ 6 := by
  intro row hrow
  let vertex : FourVertex := ⟨row, hrow⟩
  rw [fourRowDegree_actualSupportMultiplicity rowOrder
    (fourRows_actual_support_proper rowOrder hBRows) vertex]
  exact hTUpper (rowOrder vertex : Row α) (rowOrder vertex).property

theorem fourActualSupportMultiplicity_enumeration_data {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 6)
    (hThree : ∃ E ∈ T, E.card = 3)
    (hBCard : (blocker T).card ≤ 6) :
    let actual := fourActualSupportMultiplicity rowOrder
    fourMaskValid (fourMultiplicityMask actual) = true ∧
      ∃ finalDegrees,
        FourGenerated (fourMaskSupports (fourMultiplicityMask actual))
          (fourMultiplicityForMask (fourMultiplicityMask actual))
          fourDegreeStateZero actual finalDegrees := by
  let actual := fourActualSupportMultiplicity rowOrder
  have hLeaf := fourActualSupportMultiplicity_leaf_valid rowOrder
    hBRows hTRows hTUpper hThree
  have hClutter :=
    fourActualSupportMultiplicity_rows_clutter rowOrder hTClutter hBRows
  have hCovered :=
    fourActualSupportMultiplicity_active_supports_covered_of_complete
      rowOrder hTClutter hBRows four_minimal_support_index_covers_complete
  have hWeighted :=
    (fourWeightedCoverCount_le_blocker_card rowOrder hBRows).trans hBCard
  have hMask := fourMaskValid_multiplicityMask actual hLeaf hClutter hCovered hWeighted
  have hGenerated := fourGenerated_multiplicityMask actual
    (fourActualSupportMultiplicity_size rowOrder)
    (fourActualSupportMultiplicity_row_upper rowOrder hBRows hTUpper)
    hWeighted
  exact ⟨hMask, hGenerated⟩

theorem fourActualSupportMultiplicity_in_certificate_of_check {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 6)
    (hThree : ∃ E ∈ T, E.card = 3)
    (hBCard : (blocker T).card ≤ 6)
    (hCheck : fourKernelAClassificationMaskCheck
      (fourMultiplicityMask (fourActualSupportMultiplicity rowOrder)) = true) :
    fourMultiplicityInCertificate
      (fourActualSupportMultiplicity rowOrder) = true := by
  obtain ⟨hMask, finalDegrees, hGenerated⟩ :=
    fourActualSupportMultiplicity_enumeration_data rowOrder hTClutter hBRows
      hTRows hTUpper hThree hBCard
  exact fourKernelAClassificationMaskCheck_sound hMask hGenerated
    (fourActualSupportMultiplicity_leaf_valid rowOrder
      hBRows hTRows hTUpper hThree) hCheck

end AiMathLab.P0054.G419
