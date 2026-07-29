import AiMathLab.P0054G419.KernelAActualCovers

namespace AiMathLab.P0054.G419

theorem fourRowSupportMask_testBit_eq
    {row s : Nat} (hrow : row < 4) (hs : s < 14) :
    (fourRowSupportMask row).testBit s = fourSupportContains s row := by
  interval_cases row <;> interval_cases s <;> decide

theorem fourDirectionalSupportMask_testBit_eq
    {left right s : Nat} (hleft : left < 4) (hright : right < 4)
    (hs : s < 14) :
    (fourDirectionalSupportMask left right).testBit s =
      (fourSupportContains s left && !fourSupportContains s right) := by
  interval_cases left <;> interval_cases right <;> interval_cases s <;> decide

theorem fourMaskSupportDegree_multiplicityMask
    (m : FourMultiplicity) {row : Nat} (hrow : row < 4) :
    fourMaskSupportDegree (fourMultiplicityMask m) row =
      ((List.range 14).filter fun s ↦
        decide (0 < fourMultiplicityDigit m s) &&
          fourSupportContains s row).length := by
  unfold fourMaskSupportDegree
  apply congrArg List.length
  apply List.filter_congr
  intro s hs
  apply Bool.eq_iff_iff.mpr
  change
    (((fourMultiplicityMask m) &&& fourRowSupportMask row).testBit s = true ↔
      (decide (0 < fourMultiplicityDigit m s) &&
        fourSupportContains s row) = true)
  rw [Nat.testBit_land]
  simp only [Bool.and_eq_true]
  rw [fourMultiplicityMask_testBit_true_iff m (List.mem_range.mp hs),
    fourRowSupportMask_testBit_eq hrow (List.mem_range.mp hs)]
  simp

theorem length_filter_positive_le_sum {gamma : Type*}
    (values : List gamma) (f : gamma → Nat) :
    (values.filter fun x ↦ decide (0 < f x)).length ≤
      (values.map f).sum := by
  induction values with
  | nil => simp
  | cons x values ih =>
      by_cases hx : 0 < f x
      · simp [hx]
        omega
      · have hxZero : f x = 0 := Nat.eq_zero_of_not_pos hx
        simp [hx, hxZero, ih]

theorem length_filter_positive_pos_of_sum_pos {gamma : Type*}
    (values : List gamma) (f : gamma → Nat)
    (hSum : 0 < (values.map f).sum) :
    0 < (values.filter fun x ↦ decide (0 < f x)).length := by
  induction values with
  | nil => simp at hSum
  | cons x values ih =>
      by_cases hx : 0 < f x
      · simp [hx]
      · have hxZero : f x = 0 := Nat.eq_zero_of_not_pos hx
        have hTail : 0 < (values.map f).sum := by
          simpa [hxZero] using hSum
        have hLength := ih hTail
        simpa [hx] using hLength

theorem fourMaskSupportDegree_le_rowDegree
    (m : FourMultiplicity) {row : Nat} (hrow : row < 4) :
    fourMaskSupportDegree (fourMultiplicityMask m) row ≤
      fourRowDegree m row := by
  rw [fourMaskSupportDegree_multiplicityMask m hrow]
  let f : Nat → Nat := fun s ↦
    if fourSupportContains s row then fourMultiplicityDigit m s else 0
  have hFilter :
      ((List.range 14).filter fun s ↦
        decide (0 < fourMultiplicityDigit m s) &&
          fourSupportContains s row).length =
      ((List.range 14).filter fun s ↦ decide (0 < f s)).length := by
    apply congrArg List.length
    apply List.filter_congr
    intro s _hs
    by_cases hContains : fourSupportContains s row = true
    · simp [f, hContains]
    · have hFalse := Bool.eq_false_of_not_eq_true hContains
      simp [f, hFalse]
  rw [hFilter]
  exact length_filter_positive_le_sum (List.range 14) f

theorem fourMaskSupportDegree_pos_of_rowDegree_pos
    (m : FourMultiplicity) {row : Nat} (hrow : row < 4)
    (hDegree : 0 < fourRowDegree m row) :
    0 < fourMaskSupportDegree (fourMultiplicityMask m) row := by
  rw [fourMaskSupportDegree_multiplicityMask m hrow]
  let f : Nat → Nat := fun s ↦
    if fourSupportContains s row then fourMultiplicityDigit m s else 0
  have hFilter :
      ((List.range 14).filter fun s ↦
        decide (0 < fourMultiplicityDigit m s) &&
          fourSupportContains s row).length =
      ((List.range 14).filter fun s ↦ decide (0 < f s)).length := by
    apply congrArg List.length
    apply List.filter_congr
    intro s _hs
    by_cases hContains : fourSupportContains s row = true
    · simp [f, hContains]
    · have hFalse := Bool.eq_false_of_not_eq_true hContains
      simp [f, hFalse]
  rw [hFilter]
  apply length_filter_positive_pos_of_sum_pos (List.range 14) f
  simpa [f, fourRowDegree] using hDegree

theorem fourMaskRowsClutter_multiplicityMask_of_rowsClutter
    (m : FourMultiplicity) (hClutter : fourRowsClutter m = true) :
    fourMaskRowsClutter (fourMultiplicityMask m) = true := by
  unfold fourRowsClutter at hClutter
  unfold fourMaskRowsClutter
  rw [List.all_eq_true] at hClutter ⊢
  intro left hleft
  rw [List.all_eq_true]
  intro right hright
  have hPair := List.all_eq_true.mp (hClutter left hleft) right hright
  rcases Bool.or_eq_true_iff.mp hPair with hEqual | hSupport
  · exact Bool.or_eq_true_iff.mpr (Or.inl hEqual)
  · apply Bool.or_eq_true_iff.mpr
    right
    apply decide_eq_true
    obtain ⟨s, hsRange, hsWitness⟩ := List.any_eq_true.mp hSupport
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true] at hsWitness
    have hBit :
        (Nat.land (fourMultiplicityMask m)
          (fourDirectionalSupportMask left right)).testBit s = true := by
      change
        (((fourMultiplicityMask m) &&&
          fourDirectionalSupportMask left right).testBit s = true)
      rw [Nat.testBit_land]
      apply Bool.and_eq_true_iff.mpr
      constructor
      · exact (fourMultiplicityMask_testBit_true_iff m
          (List.mem_range.mp hsRange)).mpr hsWitness.1.1
      · rw [fourDirectionalSupportMask_testBit_eq
          (List.mem_range.mp hleft) (List.mem_range.mp hright)
          (List.mem_range.mp hsRange)]
        exact Bool.and_eq_true_iff.mpr
          ⟨hsWitness.1.2, hsWitness.2⟩
    intro hZero
    rw [hZero] at hBit
    simp at hBit

end AiMathLab.P0054.G419
