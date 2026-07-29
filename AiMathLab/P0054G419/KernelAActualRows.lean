import AiMathLab.P0054G419.KernelAActual

namespace AiMathLab.P0054.G419

open G413
open scoped BigOperators

theorem list_range_map_sum_eq_finset_sum_range
    (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih,
        Finset.sum_range_succ]
      simp

theorem fourRowDegree_actualSupportMultiplicity {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hProper : ∀ x ∈ fourActiveUniverse T,
      ∃ row : FourVertex, x ∉ (rowOrder row : Row α))
    (row : FourVertex) :
    fourRowDegree (fourActualSupportMultiplicity rowOrder) row.val =
      (rowOrder row : Row α).card := by
  classical
  let rowPoints : Finset α := rowOrder row
  have hPartition := Finset.card_eq_sum_card_fiberwise
    (s := rowPoints) (t := (Finset.univ : Finset FourSupportIndex))
    (f := fourActualSupportIndex rowOrder) (by simp)
  rw [show (rowOrder row : Row α).card = rowPoints.card by rfl, hPartition]
  unfold fourRowDegree
  rw [list_range_map_sum_eq_finset_sum_range]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [fourMultiplicityDigit_actualSupportMultiplicity]
  by_cases hContains : fourSupportContains s.val row.val = true
  · simp only [hContains, if_true]
    congr 1
    ext x
    simp only [fourSupportFiber, Finset.mem_filter, rowPoints]
    constructor
    · rintro ⟨hxActive, hxIndex⟩
      refine ⟨?_, hxIndex⟩
      apply (mem_fourSupportOfPoint rowOrder x row).mp
      have hSupport := fourSupport_actualSupportIndex rowOrder hProper hxActive
      rw [← hSupport, hxIndex]
      exact (mem_fourSupport s row).mpr hContains
    · rintro ⟨hxRow, hxIndex⟩
      refine ⟨?_, hxIndex⟩
      apply mem_fourActiveUniverse.mpr
      exact ⟨rowOrder row, (rowOrder row).property, hxRow⟩
  · have hFalse : fourSupportContains s.val row.val = false :=
      Bool.eq_false_of_not_eq_true hContains
    simp only [hFalse]
    symm
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxRow, hxIndex⟩ := Finset.mem_filter.mp hx
    have hxActive : x ∈ fourActiveUniverse T := by
      apply mem_fourActiveUniverse.mpr
      exact ⟨rowOrder row, (rowOrder row).property, hxRow⟩
    have hSupport := fourSupport_actualSupportIndex rowOrder hProper hxActive
    apply hContains
    apply (mem_fourSupport s row).mp
    rw [← hxIndex, hSupport]
    exact (mem_fourSupportOfPoint rowOrder x row).mpr hxRow

end AiMathLab.P0054.G419
