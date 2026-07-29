import AiMathLab.P0054G419.KernelAMaskSound

namespace AiMathLab.P0054.G419

def fourSupportListMask (supports : List Nat) : Nat :=
  (supports.map fun s ↦ 2 ^ s).sum

def fourPositiveCovers (m : FourMultiplicity) : List (List Nat) :=
  fourMinimalSupportCovers.filter fun cover ↦
    cover.all fun s ↦ decide (0 < fourMultiplicityDigit m s)

set_option maxRecDepth 100000 in
theorem four_minimal_support_cover_masks_eq :
    fourMinimalSupportCoverMasks =
      fourMinimalSupportCovers.map fourSupportListMask := by
  decide

set_option maxRecDepth 100000 in
theorem four_minimal_support_covers_sorted :
    ∀ cover ∈ fourMinimalSupportCovers, cover.SortedLT := by
  decide

set_option maxRecDepth 100000 in
theorem four_minimal_support_covers_range :
    ∀ cover ∈ fourMinimalSupportCovers, ∀ s ∈ cover, s < 14 := by
  decide

theorem fourSupportListMask_testBit_true_iff
    {supports : List Nat} (hSorted : supports.SortedLT) (s : Nat) :
    (fourSupportListMask supports).testBit s = true ↔ s ∈ supports := by
  have hBits : (fourSupportListMask supports).bitIndices = supports := by
    simpa [fourSupportListMask] using
      (Nat.bitIndices_sum_map_two_pow hSorted)
  calc
    (fourSupportListMask supports).testBit s = true ↔
        s ∈ (fourSupportListMask supports).bitIndices :=
      Nat.mem_bitIndices.symm
    _ ↔ s ∈ supports := by rw [hBits]

theorem fourSupportListMask_subset_iff
    (mask : Nat) {supports : List Nat} (hSorted : supports.SortedLT) :
    Nat.land mask (fourSupportListMask supports) =
        fourSupportListMask supports ↔
      ∀ s ∈ supports, mask.testBit s = true := by
  constructor
  · intro hSubset s hs
    have hSupportBit :=
      (fourSupportListMask_testBit_true_iff hSorted s).mpr hs
    have hBits := congrArg (fun value ↦ value.testBit s) hSubset
    change ((mask &&& fourSupportListMask supports).testBit s) =
      (fourSupportListMask supports).testBit s at hBits
    rw [Nat.testBit_land, hSupportBit] at hBits
    simpa using hBits
  · intro hSubset
    apply Nat.eq_of_testBit_eq
    intro s
    change ((mask &&& fourSupportListMask supports).testBit s) =
      (fourSupportListMask supports).testBit s
    rw [Nat.testBit_land]
    by_cases hs : s ∈ supports
    · have hSupportBit :=
        (fourSupportListMask_testBit_true_iff hSorted s).mpr hs
      simp [hSupportBit, hSubset s hs]
    · have hSupportBit :
          (fourSupportListMask supports).testBit s = false :=
        Bool.eq_false_of_not_eq_true fun hBit ↦
          hs ((fourSupportListMask_testBit_true_iff hSorted s).mp hBit)
      simp [hSupportBit]

theorem filter_map_eq_map_filter_of_predicate
    {gamma delta : Type*} (values : List gamma) (f : gamma → delta)
    (left : delta → Bool) (right : gamma → Bool)
    (hPredicate : ∀ value ∈ values, left (f value) = right value) :
    (values.map f).filter left = (values.filter right).map f := by
  induction values with
  | nil => simp
  | cons value values ih =>
      have hHead := hPredicate value (by simp)
      have hTail : ∀ item ∈ values, left (f item) = right item := by
        intro item hItem
        exact hPredicate item (by simp [hItem])
      by_cases hRight : right value = true
      · have hLeft : left (f value) = true := hHead.trans hRight
        simp [hLeft, hRight, ih hTail]
      · have hRightFalse := Bool.eq_false_of_not_eq_true hRight
        have hLeftFalse : left (f value) = false := hHead.trans hRightFalse
        simp [hLeftFalse, hRightFalse, ih hTail]

theorem fourMaskCoverCount_multiplicityMask (m : FourMultiplicity) :
    fourMaskCoverCount (fourMultiplicityMask m) =
      (fourPositiveCovers m).length := by
  unfold fourMaskCoverCount fourPositiveCovers
  rw [four_minimal_support_cover_masks_eq]
  let left : Nat → Bool := fun coverMask ↦
    decide (Nat.land (fourMultiplicityMask m) coverMask = coverMask)
  let right : List Nat → Bool := fun cover ↦
    cover.all fun s ↦ decide (0 < fourMultiplicityDigit m s)
  have hPredicate : ∀ cover ∈ fourMinimalSupportCovers,
      left (fourSupportListMask cover) = right cover := by
    intro cover hCover
    apply Bool.eq_iff_iff.mpr
    unfold left right
    rw [decide_eq_true_eq]
    rw [fourSupportListMask_subset_iff _
      (four_minimal_support_covers_sorted cover hCover)]
    rw [List.all_eq_true]
    constructor
    · intro hAll s hs
      apply decide_eq_true
      exact (fourMultiplicityMask_testBit_true_iff m
        (four_minimal_support_covers_range cover hCover s hs)).mp (hAll s hs)
    · intro hAll s hs
      apply (fourMultiplicityMask_testBit_true_iff m
        (four_minimal_support_covers_range cover hCover s hs)).mpr
      exact of_decide_eq_true (hAll s hs)
  rw [filter_map_eq_map_filter_of_predicate
    fourMinimalSupportCovers fourSupportListMask left right hPredicate]
  simp [right]

theorem length_filter_all_positive_le_sum_products
    (covers : List (List Nat)) (m : FourMultiplicity) :
    (covers.filter fun cover ↦
        cover.all fun s ↦ decide (0 < fourMultiplicityDigit m s)).length ≤
      (covers.map fun cover ↦
        (cover.map (fourMultiplicityDigit m)).prod).sum := by
  induction covers with
  | nil => simp
  | cons cover covers ih =>
      by_cases hCover :
          (cover.all fun s ↦ decide (0 < fourMultiplicityDigit m s)) = true
      · have hProduct :
            0 < (cover.map (fourMultiplicityDigit m)).prod := by
          apply List.prod_pos
          intro value hValue
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hValue
          exact of_decide_eq_true (List.all_eq_true.mp hCover s hs)
        simp [hCover]
        omega
      · simp only [List.filter_cons, hCover, Bool.false_eq_true,
          if_false, List.map_cons, List.sum_cons]
        omega

theorem four_weighted_cover_count_eq_support_covers
    (m : FourMultiplicity) :
    (fourMinimalSupportCovers.map fun cover ↦
      (cover.map (fourMultiplicityDigit m)).prod).sum =
        fourWeightedCoverCount m := by
  rw [← four_minimal_support_index_covers_values]
  simpa only [List.map_map, Function.comp_def] using
    four_weighted_cover_count_eq_index_covers m

theorem fourMaskCoverCount_le_weightedCoverCount (m : FourMultiplicity) :
    fourMaskCoverCount (fourMultiplicityMask m) ≤
      fourWeightedCoverCount m := by
  rw [fourMaskCoverCount_multiplicityMask,
    ← four_weighted_cover_count_eq_support_covers]
  exact length_filter_all_positive_le_sum_products
    fourMinimalSupportCovers m

theorem fourMaskCoverCount_pos_of_activeSupportsCovered
    (m : FourMultiplicity)
    (hActive : ∃ s < 14, 0 < fourMultiplicityDigit m s)
    (hCovered : fourActiveSupportsCovered m = true) :
    0 < fourMaskCoverCount (fourMultiplicityMask m) := by
  rw [fourMaskCoverCount_multiplicityMask]
  obtain ⟨s, hs, hsPositive⟩ := hActive
  unfold fourActiveSupportsCovered at hCovered
  have hsCovered := List.all_eq_true.mp hCovered s (List.mem_range.mpr hs)
  have hsNonzero : fourMultiplicityDigit m s ≠ 0 := Nat.ne_of_gt hsPositive
  simp only [decide_eq_false_iff_not.mpr hsNonzero, Bool.false_or] at hsCovered
  obtain ⟨cover, hCover, hCoverWitness⟩ := List.any_eq_true.mp hsCovered
  have hCoverPositive := Bool.and_eq_true_iff.mp hCoverWitness |>.2
  apply List.length_pos_of_mem
  exact List.mem_filter.mpr ⟨hCover, hCoverPositive⟩

theorem foldl_select_eq_filter_foldl {gamma delta : Type*}
    (values : List gamma) (predicate : gamma → Prop)
    [DecidablePred predicate] (operation : delta → gamma → delta)
    (initial : delta) :
    values.foldl
        (fun state value ↦
          if predicate value then operation state value else state) initial =
      (values.filter fun value ↦ decide (predicate value)).foldl
        operation initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values ih =>
      by_cases hPredicate : predicate value
      · simp [hPredicate, ih]
      · simp [hPredicate, ih]

theorem testBit_foldl_lor_true_of_initial
    (values : List Nat) (initial bit : Nat)
    (hInitial : initial.testBit bit = true) :
    (values.foldl Nat.lor initial).testBit bit = true := by
  induction values generalizing initial with
  | nil => exact hInitial
  | cons value values ih =>
      apply ih
      change ((initial ||| value).testBit bit = true)
      rw [Nat.testBit_lor]
      simp [hInitial]

theorem testBit_foldl_lor_true_of_mem
    (values : List Nat) (initial value bit : Nat)
    (hValue : value ∈ values) (hBit : value.testBit bit = true) :
    (values.foldl Nat.lor initial).testBit bit = true := by
  induction values generalizing initial with
  | nil => simp at hValue
  | cons head values ih =>
      rcases List.mem_cons.mp hValue with rfl | hValue
      · apply testBit_foldl_lor_true_of_initial values
          (Nat.lor initial value) bit
        change ((initial ||| value).testBit bit = true)
        rw [Nat.testBit_lor]
        simp [hBit]
      · exact ih (Nat.lor initial head) hValue

theorem testBit_foldl_lor_false
    (values : List Nat) (initial bit : Nat)
    (hInitial : initial.testBit bit = false)
    (hValues : ∀ value ∈ values, value.testBit bit = false) :
    (values.foldl Nat.lor initial).testBit bit = false := by
  induction values generalizing initial with
  | nil => exact hInitial
  | cons value values ih =>
      apply ih
      · change ((initial ||| value).testBit bit = false)
        rw [Nat.testBit_lor]
        simp [hInitial, hValues value (by simp)]
      · intro item hItem
        exact hValues item (by simp [hItem])

theorem testBit_true_of_land_eq_right
    {mask value bit : Nat} (hSubset : Nat.land mask value = value)
    (hBit : value.testBit bit = true) :
    mask.testBit bit = true := by
  have hBits := congrArg (fun number ↦ number.testBit bit) hSubset
  change ((mask &&& value).testBit bit) = value.testBit bit at hBits
  rw [Nat.testBit_land, hBit] at hBits
  simpa using hBits

theorem fourMaskCoveredUnion_multiplicityMask_of_activeSupportsCovered
    (m : FourMultiplicity) (hCovered : fourActiveSupportsCovered m = true) :
    fourMaskCoveredUnion (fourMultiplicityMask m) =
      fourMultiplicityMask m := by
  unfold fourMaskCoveredUnion
  rw [foldl_select_eq_filter_foldl]
  apply Nat.eq_of_testBit_eq
  intro s
  by_cases hMaskBit : (fourMultiplicityMask m).testBit s = true
  · have hsIndices : s ∈ (fourMultiplicityMask m).bitIndices :=
      Nat.mem_bitIndices.mpr hMaskBit
    have hsActive : s ∈ fourActiveSupportFinset m := by
      rw [← fourMultiplicityMask_bitIndices]
      exact List.mem_toFinset.mpr hsIndices
    obtain ⟨hsRange, hsPositive⟩ := Finset.mem_filter.mp hsActive
    have hsLt := Finset.mem_range.mp hsRange
    unfold fourActiveSupportsCovered at hCovered
    have hsCovered := List.all_eq_true.mp hCovered s (List.mem_range.mpr hsLt)
    have hsNonzero : fourMultiplicityDigit m s ≠ 0 := Nat.ne_of_gt hsPositive
    simp only [decide_eq_false_iff_not.mpr hsNonzero,
      Bool.false_or] at hsCovered
    obtain ⟨cover, hCover, hCoverWitness⟩ := List.any_eq_true.mp hsCovered
    obtain ⟨hsCover, hCoverPositive⟩ :=
      Bool.and_eq_true_iff.mp hCoverWitness
    have hsCoverMem : s ∈ cover := of_decide_eq_true hsCover
    let coverMask := fourSupportListMask cover
    have hCoverMaskMem : coverMask ∈ fourMinimalSupportCoverMasks := by
      rw [four_minimal_support_cover_masks_eq]
      exact List.mem_map.mpr ⟨cover, hCover, rfl⟩
    have hCoverMaskSubset :
        Nat.land (fourMultiplicityMask m) coverMask = coverMask := by
      apply (fourSupportListMask_subset_iff _
        (four_minimal_support_covers_sorted cover hCover)).mpr
      intro t ht
      apply (fourMultiplicityMask_testBit_true_iff m
        (four_minimal_support_covers_range cover hCover t ht)).mpr
      exact of_decide_eq_true (List.all_eq_true.mp hCoverPositive t ht)
    have hCoverMaskSelected :
        coverMask ∈ fourMinimalSupportCoverMasks.filter fun value ↦
          decide (Nat.land (fourMultiplicityMask m) value = value) :=
      List.mem_filter.mpr
        ⟨hCoverMaskMem, decide_eq_true hCoverMaskSubset⟩
    have hCoverMaskBit : coverMask.testBit s = true :=
      (fourSupportListMask_testBit_true_iff
        (four_minimal_support_covers_sorted cover hCover) s).mpr hsCoverMem
    rw [hMaskBit]
    exact testBit_foldl_lor_true_of_mem _ 0 coverMask s
      hCoverMaskSelected hCoverMaskBit
  · have hMaskFalse : (fourMultiplicityMask m).testBit s = false :=
      Bool.eq_false_of_not_eq_true hMaskBit
    rw [hMaskFalse]
    apply testBit_foldl_lor_false
    · simp
    · intro coverMask hCoverMask
      obtain ⟨_coverMaskMem, hSubset⟩ := List.mem_filter.mp hCoverMask
      have hSubsetProp := of_decide_eq_true hSubset
      apply Bool.eq_false_of_not_eq_true
      intro hCoverBit
      exact hMaskBit (testBit_true_of_land_eq_right hSubsetProp hCoverBit)

theorem fourMaskValid_multiplicityMask
    (m : FourMultiplicity)
    (hLeaf : fourMultiplicityLeafValid m = true)
    (hClutter : fourRowsClutter m = true)
    (hCovered : fourActiveSupportsCovered m = true)
    (hWeighted : fourWeightedCoverCount m ≤ 6) :
    fourMaskValid (fourMultiplicityMask m) = true := by
  unfold fourMultiplicityLeafValid at hLeaf
  have hDegreeAll := (Bool.and_eq_true_iff.mp hLeaf).1
  have hRowBounds : ∀ row < 4,
      3 ≤ fourRowDegree m row ∧ fourRowDegree m row ≤ 6 := by
    intro row hrow
    apply of_decide_eq_true
    exact List.all_eq_true.mp hDegreeAll (fourRowDegree m row)
      (List.mem_map.mpr ⟨row, List.mem_range.mpr hrow, rfl⟩)
  have hMaskDegreeAll :
      ((List.range 4).map
        (fourMaskSupportDegree (fourMultiplicityMask m))).all
          (fun degree ↦ decide (0 < degree ∧ degree ≤ 6)) = true := by
    rw [List.all_eq_true]
    intro degree hDegree
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hDegree
    have hrowLt := List.mem_range.mp hrow
    apply decide_eq_true
    exact ⟨fourMaskSupportDegree_pos_of_rowDegree_pos m hrowLt
        (by have hLower := (hRowBounds row hrowLt).1; omega),
      (fourMaskSupportDegree_le_rowDegree m hrowLt).trans
        (hRowBounds row hrowLt).2⟩
  have hMaskNonzero : fourMultiplicityMask m ≠ 0 := by
    have hPositive := fourMaskSupportDegree_pos_of_rowDegree_pos m
      (row := 0) (by omega) (by have := (hRowBounds 0 (by omega)).1; omega)
    intro hZero
    unfold fourMaskSupportDegree at hPositive
    simp [hZero] at hPositive
  have hActive : ∃ s < 14, 0 < fourMultiplicityDigit m s := by
    by_contra hExists
    have hActiveEmpty : fourActiveSupportFinset m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      obtain ⟨hsRange, hsPositive⟩ := Finset.mem_filter.mp hs
      exact hExists ⟨s, Finset.mem_range.mp hsRange, hsPositive⟩
    apply hMaskNonzero
    simp [fourMultiplicityMask, hActiveEmpty]
  have hCoverCountPositive :=
    fourMaskCoverCount_pos_of_activeSupportsCovered m hActive hCovered
  have hCoverCountUpper :=
    (fourMaskCoverCount_le_weightedCoverCount m).trans hWeighted
  have hMaskClutter :=
    fourMaskRowsClutter_multiplicityMask_of_rowsClutter m hClutter
  have hCoveredUnion :=
    fourMaskCoveredUnion_multiplicityMask_of_activeSupportsCovered m hCovered
  unfold fourMaskValid
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true hCoveredUnion⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true ⟨hCoverCountPositive, hCoverCountUpper⟩⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hMaskClutter⟩
  apply Bool.and_eq_true_iff.mpr
  exact ⟨decide_eq_true hMaskNonzero, hMaskDegreeAll⟩

end AiMathLab.P0054.G419
