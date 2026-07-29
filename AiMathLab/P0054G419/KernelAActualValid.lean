import AiMathLab.P0054G419.KernelAActualProper

namespace AiMathLab.P0054.G419

open G413

set_option maxHeartbeats 2000000 in
-- Expanding the four symbolic row-degree sums exceeds the default budget.
theorem fourActualSupportMultiplicity_leaf_valid {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    (hTRows : RowsCardAtLeast T 3)
    (hTUpper : ∀ E ∈ T, E.card ≤ 6)
    (hThree : ∃ E ∈ T, E.card = 3) :
    fourMultiplicityLeafValid (fourActualSupportMultiplicity rowOrder) = true := by
  let hProper := fourRows_actual_support_proper rowOrder hBRows
  unfold fourMultiplicityLeafValid
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [List.all_eq_true]
    intro degree hDegree
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hDegree
    let row : FourVertex := ⟨n, List.mem_range.mp hn⟩
    have hDegree := fourRowDegree_actualSupportMultiplicity rowOrder hProper row
    have hLower := hTRows (rowOrder row : Row α) (rowOrder row).property
    have hUpper := hTUpper (rowOrder row : Row α) (rowOrder row).property
    apply decide_eq_true
    change
      3 ≤ fourRowDegree (fourActualSupportMultiplicity rowOrder) row.val ∧
        fourRowDegree (fourActualSupportMultiplicity rowOrder) row.val ≤ 6
    rw [hDegree]
    exact ⟨hLower, hUpper⟩
  · apply List.any_eq_true.mpr
    obtain ⟨E, hET, hECard⟩ := hThree
    let e : T := ⟨E, hET⟩
    obtain ⟨row, hrow⟩ := rowOrder.surjective e
    refine ⟨fourRowDegree (fourActualSupportMultiplicity rowOrder) row.val,
      List.mem_map.mpr ⟨row.val, List.mem_range.mpr row.isLt, rfl⟩, ?_⟩
    apply decide_eq_true
    rw [fourRowDegree_actualSupportMultiplicity rowOrder hProper row]
    simpa [e, hrow] using hECard

end AiMathLab.P0054.G419
