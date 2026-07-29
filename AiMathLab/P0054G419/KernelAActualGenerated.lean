import AiMathLab.P0054G419.KernelACoverMaskSound

namespace AiMathLab.P0054.G419

def fourRemainingRowDegree
    (m : FourMultiplicity) (supports : List Nat) (row : Nat) : Nat :=
  (supports.map fun s ↦
    if fourSupportContains s row then fourMultiplicityDigit m s else 0).sum

theorem fourMultiplicityDigit_set!
    (m : FourMultiplicity) {s t k : Nat}
    (hSize : m.size = 14) (hs : s < 14) (ht : t < 14) :
    fourMultiplicityDigit (m.set! s k) t =
      if t = s then k else fourMultiplicityDigit m t := by
  simp only [fourMultiplicityDigit, Array.set!_eq_setIfInBounds,
    Array.getD_eq_getD_getElem?]
  by_cases hts : t = s
  · subst t
    rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
    simp
  · rw [if_neg hts, Array.getElem?_setIfInBounds_ne (Ne.symm hts)]

theorem addFourSupportDegree_getD
    (degrees : FourDegreeState) (s k : Nat) {row : Nat} (hrow : row < 4) :
    (addFourSupportDegree degrees s k).getD row 0 =
      degrees.getD row 0 + if fourSupportContains s row then k else 0 := by
  simp [addFourSupportDegree, hrow]

theorem exists_fourSupportContains {s : Nat} (hs : s < 14) :
    ∃ row < 4, fourSupportContains s row = true := by
  interval_cases s <;> decide

theorem fourMultiplicityDigit_le_rowDegree
    (m : FourMultiplicity) {s row : Nat}
    (hs : s < 14) (hContains : fourSupportContains s row = true) :
    fourMultiplicityDigit m s ≤ fourRowDegree m row := by
  unfold fourRowDegree
  apply List.le_sum_of_mem
  apply List.mem_map.mpr
  exact ⟨s, List.mem_range.mpr hs, by simp [hContains]⟩

theorem fourRemainingRowDegree_cons
    (m : FourMultiplicity) (s : Nat) (supports : List Nat) (row : Nat) :
    fourRemainingRowDegree m (s :: supports) row =
      (if fourSupportContains s row then fourMultiplicityDigit m s else 0) +
        fourRemainingRowDegree m supports row := by
  rfl

theorem fourRemainingRowDegree_filter_positive
    (m : FourMultiplicity) (values : List Nat) (row : Nat) :
    fourRemainingRowDegree m
        (values.filter fun s ↦ decide (0 < fourMultiplicityDigit m s)) row =
      ((values.map fun s ↦
        if fourSupportContains s row then fourMultiplicityDigit m s else 0).sum) := by
  induction values with
  | nil => rfl
  | cons s values ih =>
      by_cases hs : 0 < fourMultiplicityDigit m s
      · have hDecide : decide (0 < fourMultiplicityDigit m s) = true :=
          decide_eq_true hs
        rw [List.filter_cons, hDecide]
        simp only [Bool.true_eq, if_true, fourRemainingRowDegree_cons,
          List.map_cons, List.sum_cons, ih]
      · have hsZero := Nat.eq_zero_of_not_pos hs
        have hDecide : decide (0 < fourMultiplicityDigit m s) = false :=
          decide_eq_false hs
        rw [List.filter_cons, hDecide]
        simp only [Bool.false_eq_true, if_false, List.map_cons, List.sum_cons, ih]
        simp [hsZero]

theorem fourRemainingRowDegree_maskSupports
    (m : FourMultiplicity) (row : Nat) :
    fourRemainingRowDegree m (fourMaskSupports (fourMultiplicityMask m)) row =
      fourRowDegree m row := by
  rw [fourMaskSupports_multiplicityMask]
  exact fourRemainingRowDegree_filter_positive m (List.range 14) row

theorem fourProductDigits_mono
    {left right : FourMultiplicity} (supports : List Nat)
    (hRange : ∀ s ∈ supports, s < 14)
    (hDigits : ∀ s < 14,
      fourMultiplicityDigit left s ≤ fourMultiplicityDigit right s) :
    (supports.map (fourMultiplicityDigit left)).prod ≤
      (supports.map (fourMultiplicityDigit right)).prod := by
  induction supports with
  | nil => simp
  | cons s supports ih =>
      simp only [List.map_cons, List.prod_cons]
      apply Nat.mul_le_mul
      · exact hDigits s (hRange s (by simp))
      · apply ih
        intro t ht
        exact hRange t (by simp [ht])

theorem fourWeightedCoverCount_mono
    {left right : FourMultiplicity}
    (hDigits : ∀ s < 14,
      fourMultiplicityDigit left s ≤ fourMultiplicityDigit right s) :
    fourWeightedCoverCount left ≤ fourWeightedCoverCount right := by
  rw [← four_weighted_cover_count_eq_support_covers,
    ← four_weighted_cover_count_eq_support_covers]
  suffices h : ∀ covers : List (List Nat),
      (∀ cover ∈ covers, ∀ s ∈ cover, s < 14) →
      (covers.map fun cover ↦
          (cover.map (fourMultiplicityDigit left)).prod).sum ≤
        (covers.map fun cover ↦
          (cover.map (fourMultiplicityDigit right)).prod).sum by
    exact h fourMinimalSupportCovers four_minimal_support_covers_range
  intro covers hRange
  induction covers with
  | nil => simp
  | cons cover covers ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · apply fourProductDigits_mono cover
        · intro s hs
          exact hRange cover (by simp) s hs
        · exact hDigits
      · apply ih
        intro item hItem
        exact hRange item (by simp [hItem])

theorem fourGenerated_suffix
    (actual current : FourMultiplicity) (remaining : List Nat)
    (degrees : FourDegreeState)
    (hActualSize : actual.size = 14)
    (hCurrentSize : current.size = 14)
    (hRemainingRange : ∀ s ∈ remaining, s < 14)
    (hRemainingPositive : ∀ s ∈ remaining,
      0 < fourMultiplicityDigit actual s)
    (hCurrentLe : ∀ s < 14,
      fourMultiplicityDigit current s ≤ fourMultiplicityDigit actual s)
    (hCurrentDone : ∀ s < 14, s ∉ remaining →
      fourMultiplicityDigit current s = fourMultiplicityDigit actual s)
    (hDegreeInvariant : ∀ row < 4,
      degrees.getD row 0 + fourRemainingRowDegree actual remaining row =
        fourRowDegree actual row)
    (hRowUpper : ∀ row < 4, fourRowDegree actual row ≤ 6)
    (hWeighted : fourWeightedCoverCount actual ≤ 6) :
    ∃ finalDegrees,
      FourGenerated remaining current degrees actual finalDegrees := by
  induction remaining generalizing current degrees with
  | nil =>
      have hCurrent : current = actual := by
        apply Array.ext
        · omega
        · intro i hiCurrent hiActual
          have hi : i < 14 := by omega
          have hDigit := hCurrentDone i hi (by simp)
          simpa [fourMultiplicityDigit, hCurrentSize, hActualSize, hi] using hDigit
      subst current
      exact ⟨degrees, FourGenerated.nil _ _⟩
  | cons s remaining ih =>
      let k := fourMultiplicityDigit actual s
      have hsRange : s < 14 := hRemainingRange s (by simp)
      have hkPositive : 0 < k := hRemainingPositive s (by simp)
      have hkUpper : k ≤ 6 := by
        obtain ⟨row, hrow, hContains⟩ := exists_fourSupportContains hsRange
        exact (fourMultiplicityDigit_le_rowDegree actual hsRange hContains).trans
          (hRowUpper row hrow)
      have hkRange : k ∈ (List.range 6).map (· + 1) := by
        apply List.mem_map.mpr
        refine ⟨k - 1, List.mem_range.mpr (by omega), by omega⟩
      have hDegreeCaps :
          ((List.range 4).all fun row ↦
            !fourSupportContains s row ||
              decide (degrees.getD row 0 + k ≤ 6)) = true := by
        rw [List.all_eq_true]
        intro row hrow
        have hrowLt := List.mem_range.mp hrow
        by_cases hContains : fourSupportContains s row = true
        · have hInvariant := hDegreeInvariant row hrowLt
          rw [fourRemainingRowDegree_cons, hContains] at hInvariant
          simp only [if_true] at hInvariant
          apply Bool.or_eq_true_iff.mpr
          right
          apply decide_eq_true
          have hUpper := hRowUpper row hrowLt
          omega
        · have hContainsFalse := Bool.eq_false_of_not_eq_true hContains
          apply Bool.or_eq_true_iff.mpr
          left
          simp [hContainsFalse]
      let next := current.set! s k
      have hNextSize : next.size = 14 := by
        simp [next, hCurrentSize]
      have hNextLe : ∀ t < 14,
          fourMultiplicityDigit next t ≤ fourMultiplicityDigit actual t := by
        intro t ht
        rw [fourMultiplicityDigit_set! current hCurrentSize hsRange ht]
        by_cases hts : t = s
        · simp [hts, k]
        · simp [hts, hCurrentLe t ht]
      have hNextWeighted : fourWeightedCoverCount next ≤ 6 :=
        (fourWeightedCoverCount_mono hNextLe).trans hWeighted
      have hChoice : k ∈ fourMultiplicityChoices current degrees s := by
        apply List.mem_filter.mpr
        refine ⟨hkRange, Bool.and_eq_true_iff.mpr ⟨hDegreeCaps, ?_⟩⟩
        exact decide_eq_true hNextWeighted
      have hTailRange : ∀ t ∈ remaining, t < 14 := by
        intro t ht
        exact hRemainingRange t (by simp [ht])
      have hTailPositive : ∀ t ∈ remaining,
          0 < fourMultiplicityDigit actual t := by
        intro t ht
        exact hRemainingPositive t (by simp [ht])
      have hNextDone : ∀ t < 14, t ∉ remaining →
          fourMultiplicityDigit next t = fourMultiplicityDigit actual t := by
        intro t ht hNotTail
        rw [fourMultiplicityDigit_set! current hCurrentSize hsRange ht]
        by_cases hts : t = s
        · simp [hts, k]
        · simp only [if_neg hts]
          exact hCurrentDone t ht (by simp [hts, hNotTail])
      have hNextDegreeInvariant : ∀ row < 4,
          (addFourSupportDegree degrees s k).getD row 0 +
              fourRemainingRowDegree actual remaining row =
            fourRowDegree actual row := by
        intro row hrow
        rw [addFourSupportDegree_getD degrees s k hrow]
        have hInvariant := hDegreeInvariant row hrow
        rw [fourRemainingRowDegree_cons] at hInvariant
        simpa [k, Nat.add_assoc] using hInvariant
      obtain ⟨finalDegrees, hGenerated⟩ := ih next
        (addFourSupportDegree degrees s k) hNextSize hTailRange hTailPositive
        hNextLe hNextDone hNextDegreeInvariant
      exact ⟨finalDegrees, FourGenerated.cons hChoice hGenerated⟩

theorem fourGenerated_multiplicityMask
    (m : FourMultiplicity) (hSize : m.size = 14)
    (hRowUpper : ∀ row < 4, fourRowDegree m row ≤ 6)
    (hWeighted : fourWeightedCoverCount m ≤ 6) :
    ∃ finalDegrees,
      FourGenerated (fourMaskSupports (fourMultiplicityMask m))
        (fourMultiplicityForMask (fourMultiplicityMask m))
        fourDegreeStateZero m finalDegrees := by
  apply fourGenerated_suffix m
  · exact hSize
  · simp [fourMultiplicityForMask]
  · intro s hs
    exact List.mem_range.mp (List.mem_of_mem_filter hs)
  · intro s hs
    rw [fourMaskSupports_multiplicityMask] at hs
    exact of_decide_eq_true (List.mem_filter.mp hs).2
  · intro s hs
    rw [fourMultiplicityForMask_multiplicityMask_digit m hs]
    split <;> omega
  · intro s hs hNotSupport
    have hsZero : fourMultiplicityDigit m s = 0 := by
      by_contra hsNonzero
      have hsPositive := Nat.pos_of_ne_zero hsNonzero
      apply hNotSupport
      rw [fourMaskSupports_multiplicityMask]
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr hs, decide_eq_true hsPositive⟩
    rw [fourMultiplicityForMask_multiplicityMask_digit m hs]
    simp [hsZero]
  · intro row hrow
    rw [fourRemainingRowDegree_maskSupports]
    simp [fourDegreeStateZero, hrow]
  · exact hRowUpper
  · exact hWeighted

end AiMathLab.P0054.G419
