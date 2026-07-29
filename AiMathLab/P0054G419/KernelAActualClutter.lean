import AiMathLab.P0054G419.KernelALift
import AiMathLab.P0054G419.KernelAMask

namespace AiMathLab.P0054.G419

open G413

theorem fourActualSupportMultiplicity_rows_clutter {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hTClutter : IsClutter T)
    (hBRows : RowsCardAtLeast (blocker T) 2) :
    fourRowsClutter (fourActualSupportMultiplicity rowOrder) = true := by
  classical
  let hProper := fourRows_actual_support_proper rowOrder hBRows
  unfold fourRowsClutter
  rw [List.all_eq_true]
  intro left hLeft
  rw [List.all_eq_true]
  intro right hRight
  let l : FourVertex := ⟨left, List.mem_range.mp hLeft⟩
  let r : FourVertex := ⟨right, List.mem_range.mp hRight⟩
  by_cases hlr : left = right
  · simp [hlr]
  · have hRowsNe : (rowOrder l : Row α) ≠ (rowOrder r : Row α) := by
      intro hRows
      have hSubtype : rowOrder l = rowOrder r := Subtype.ext hRows
      have hVertices : l = r := rowOrder.injective hSubtype
      exact hlr (congrArg Fin.val hVertices)
    have hNotSubset : ¬(rowOrder l : Row α) ⊆ (rowOrder r : Row α) := by
      intro hSubset
      exact hRowsNe (hTClutter (rowOrder l).property (rowOrder r).property hSubset)
    obtain ⟨x, hxLeft, hxRight⟩ := Finset.not_subset.mp hNotSubset
    have hxActive : x ∈ fourActiveUniverse T :=
      mem_fourActiveUniverse.mpr ⟨rowOrder l, (rowOrder l).property, hxLeft⟩
    let s := fourActualSupportIndex rowOrder x
    have hxFiber : x ∈ fourSupportFiber rowOrder s := by
      exact Finset.mem_filter.mpr ⟨hxActive, rfl⟩
    have hsPositive :
        0 < fourMultiplicityDigit (fourActualSupportMultiplicity rowOrder) s.val := by
      rw [fourMultiplicityDigit_actualSupportMultiplicity]
      exact Finset.card_pos.mpr ⟨x, hxFiber⟩
    have hsLeft : fourSupportContains s.val left = true := by
      apply (mem_fourSupport s l).mp
      rw [fourSupport_actualSupportIndex rowOrder hProper hxActive]
      exact (mem_fourSupportOfPoint rowOrder x l).mpr hxLeft
    have hsRight : fourSupportContains s.val right = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hsRight
      apply hxRight
      apply (mem_fourSupportOfPoint rowOrder x r).mp
      rw [← fourSupport_actualSupportIndex rowOrder hProper hxActive]
      exact (mem_fourSupport s r).mpr hsRight
    apply Bool.or_eq_true_iff.mpr
    right
    apply List.any_eq_true.mpr
    exact ⟨s.val, List.mem_range.mpr s.isLt, by
      simp [hsPositive, hsLeft, hsRight]⟩

end AiMathLab.P0054.G419
