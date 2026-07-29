import AiMathLab.P0054G420.MiddleFourDegreeFourBridge

namespace AiMathLab.P0054.G420

open G413 G419

def smallFourMultiplicityChoices (pairBound : Nat)
    (m : FourMultiplicity) (degrees : FourDegreeState) (s : Nat) : List Nat :=
  ((List.range 5).map (· + 1)).filter fun k ↦
    ((List.range 4).all fun row ↦
      !fourSupportContains s row || decide (degrees.getD row 0 + k ≤ 5)) &&
      decide (fourWeightedCoverCount (m.set! s k) ≤ 5) &&
        decide (fourPairCoverCount (m.set! s k) ≤ pairBound)

def smallFourMaskValid (pairBound mask : Nat) : Bool :=
  let supportDegrees := (List.range 4).map (fourMaskSupportDegree mask)
  decide (mask ≠ 0) &&
    supportDegrees.all (fun degree ↦ decide (0 < degree ∧ degree ≤ 5)) &&
      fourMaskRowsClutter mask &&
        decide (0 < fourMaskCoverCount mask ∧ fourMaskCoverCount mask ≤ 5) &&
          decide (middleFourMaskPairCoverCount mask ≤ pairBound) &&
            decide (fourMaskCoveredUnion mask = mask)

def smallFourClassificationAux (pairBound : Nat)
    (leaf accept : FourMultiplicity → Bool) :
    List Nat → FourMultiplicity → FourDegreeState → Bool
  | [], m, _ => !leaf m || accept m
  | s :: supports, m, degrees =>
      (smallFourMultiplicityChoices pairBound m degrees s).all fun k ↦
        smallFourClassificationAux pairBound leaf accept supports (m.set! s k)
          (addFourSupportDegree degrees s k)

def smallFourClassificationMaskCheck (pairBound : Nat)
    (leaf accept : FourMultiplicity → Bool) (mask : Nat) : Bool :=
  !smallFourMaskValid pairBound mask ||
    smallFourClassificationAux pairBound leaf accept (fourMaskSupports mask)
      (fourMultiplicityForMask mask) fourDegreeStateZero

inductive SmallFourGenerated (pairBound : Nat) :
    List Nat → FourMultiplicity → FourDegreeState →
      FourMultiplicity → FourDegreeState → Prop
  | nil (m degrees) : SmallFourGenerated pairBound [] m degrees m degrees
  | cons {s : Nat} {supports : List Nat} {m finalM : FourMultiplicity}
      {degrees finalDegrees : FourDegreeState} {k : Nat}
      (hChoice : k ∈ smallFourMultiplicityChoices pairBound m degrees s)
      (hGenerated : SmallFourGenerated pairBound supports (m.set! s k)
        (addFourSupportDegree degrees s k) finalM finalDegrees) :
      SmallFourGenerated pairBound (s :: supports) m degrees finalM finalDegrees

theorem smallFourClassificationAux_sound
    {pairBound : Nat} {leaf accept : FourMultiplicity → Bool}
    {supports : List Nat} {m finalM : FourMultiplicity}
    {degrees finalDegrees : FourDegreeState}
    (hGenerated : SmallFourGenerated pairBound supports m degrees finalM finalDegrees)
    (hCheck : smallFourClassificationAux pairBound leaf accept supports m degrees = true)
    (hLeaf : leaf finalM = true) :
    accept finalM = true := by
  induction hGenerated with
  | nil => simpa [smallFourClassificationAux, hLeaf] using hCheck
  | @cons s supports m finalM degrees finalDegrees k hChoice hGenerated ih =>
      have hAll := hCheck
      simp only [smallFourClassificationAux, List.all_eq_true] at hAll
      exact ih (hAll k hChoice) hLeaf

theorem smallFourClassificationMaskCheck_sound
    {pairBound : Nat} {leaf accept : FourMultiplicity → Bool}
    {mask : Nat} {m : FourMultiplicity} {degrees : FourDegreeState}
    (hMask : smallFourMaskValid pairBound mask = true)
    (hGenerated : SmallFourGenerated pairBound (fourMaskSupports mask)
      (fourMultiplicityForMask mask) fourDegreeStateZero m degrees)
    (hLeaf : leaf m = true)
    (hCheck : smallFourClassificationMaskCheck pairBound leaf accept mask = true) :
    accept m = true := by
  apply smallFourClassificationAux_sound hGenerated (hLeaf := hLeaf)
  simpa [smallFourClassificationMaskCheck, hMask] using hCheck

theorem smallFourGenerated_suffix
    (pairBound : Nat)
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
    (hRowUpper : ∀ row < 4, fourRowDegree actual row ≤ 5)
    (hWeighted : fourWeightedCoverCount actual ≤ 5)
    (hPair : fourPairCoverCount actual ≤ pairBound) :
    ∃ finalDegrees,
      SmallFourGenerated pairBound remaining current degrees actual finalDegrees := by
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
      exact ⟨degrees, SmallFourGenerated.nil _ _⟩
  | cons s remaining ih =>
      let k := fourMultiplicityDigit actual s
      have hsRange : s < 14 := hRemainingRange s (by simp)
      have hkPositive : 0 < k := hRemainingPositive s (by simp)
      have hkUpper : k ≤ 5 := by
        obtain ⟨row, hrow, hContains⟩ := exists_fourSupportContains hsRange
        exact (fourMultiplicityDigit_le_rowDegree actual hsRange hContains).trans
          (hRowUpper row hrow)
      have hkRange : k ∈ (List.range 5).map (· + 1) := by
        apply List.mem_map.mpr
        exact ⟨k - 1, List.mem_range.mpr (by omega), by omega⟩
      have hDegreeCaps :
          ((List.range 4).all fun row ↦
            !fourSupportContains s row ||
              decide (degrees.getD row 0 + k ≤ 5)) = true := by
        rw [List.all_eq_true]
        intro row hrow
        have hrowLt := List.mem_range.mp hrow
        by_cases hContains : fourSupportContains s row = true
        · have hInvariant := hDegreeInvariant row hrowLt
          rw [fourRemainingRowDegree_cons, hContains] at hInvariant
          simp only [if_true] at hInvariant
          exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true (by
            have hUpper := hRowUpper row hrowLt
            omega)))
        · exact Bool.or_eq_true_iff.mpr (Or.inl (by
            simp [Bool.eq_false_of_not_eq_true hContains]))
      let next := current.set! s k
      have hNextSize : next.size = 14 := by simp [next, hCurrentSize]
      have hNextLe : ∀ t < 14,
          fourMultiplicityDigit next t ≤ fourMultiplicityDigit actual t := by
        intro t ht
        rw [fourMultiplicityDigit_set! current hCurrentSize hsRange ht]
        by_cases hts : t = s
        · simp [hts, k]
        · simp [hts, hCurrentLe t ht]
      have hNextWeighted : fourWeightedCoverCount next ≤ 5 :=
        (fourWeightedCoverCount_mono hNextLe).trans hWeighted
      have hNextPair : fourPairCoverCount next ≤ pairBound :=
        (fourPairCoverCount_mono hNextLe).trans hPair
      have hChoice : k ∈ smallFourMultiplicityChoices pairBound current degrees s := by
        apply List.mem_filter.mpr
        refine ⟨hkRange, Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true hNextPair⟩⟩
        exact Bool.and_eq_true_iff.mpr
          ⟨hDegreeCaps, decide_eq_true hNextWeighted⟩
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
      exact ⟨finalDegrees, SmallFourGenerated.cons hChoice hGenerated⟩

theorem smallFourGenerated_multiplicityMask
    (pairBound : Nat) (m : FourMultiplicity) (hSize : m.size = 14)
    (hRowUpper : ∀ row < 4, fourRowDegree m row ≤ 5)
    (hWeighted : fourWeightedCoverCount m ≤ 5)
    (hPair : fourPairCoverCount m ≤ pairBound) :
    ∃ finalDegrees,
      SmallFourGenerated pairBound (fourMaskSupports (fourMultiplicityMask m))
        (fourMultiplicityForMask (fourMultiplicityMask m))
        fourDegreeStateZero m finalDegrees := by
  apply smallFourGenerated_suffix pairBound m
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
      apply hNotSupport
      rw [fourMaskSupports_multiplicityMask]
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr hs, decide_eq_true (Nat.pos_of_ne_zero hsNonzero)⟩
    rw [fourMultiplicityForMask_multiplicityMask_digit m hs]
    simp [hsZero]
  · intro row hrow
    rw [fourRemainingRowDegree_maskSupports]
    simp [fourDegreeStateZero, hrow]
  · exact hRowUpper
  · exact hWeighted
  · exact hPair

theorem smallFourMaskValid_multiplicityMask
    (pairBound : Nat) (m : FourMultiplicity)
    (hRowBounds : ∀ row < 4,
      0 < fourRowDegree m row ∧ fourRowDegree m row ≤ 5)
    (hClutter : fourRowsClutter m = true)
    (hCovered : fourActiveSupportsCovered m = true)
    (hWeighted : fourWeightedCoverCount m ≤ 5)
    (hPair : fourPairCoverCount m ≤ pairBound) :
    smallFourMaskValid pairBound (fourMultiplicityMask m) = true := by
  have hMaskDegreeAll :
      ((List.range 4).map
        (fourMaskSupportDegree (fourMultiplicityMask m))).all
          (fun degree ↦ decide (0 < degree ∧ degree ≤ 5)) = true := by
    rw [List.all_eq_true]
    intro degree hDegree
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hDegree
    have hrowLt := List.mem_range.mp hrow
    exact decide_eq_true
      ⟨fourMaskSupportDegree_pos_of_rowDegree_pos m hrowLt
        (hRowBounds row hrowLt).1,
      (fourMaskSupportDegree_le_rowDegree m hrowLt).trans
        (hRowBounds row hrowLt).2⟩
  have hMaskNonzero : fourMultiplicityMask m ≠ 0 := by
    have hPositive := fourMaskSupportDegree_pos_of_rowDegree_pos m
      (row := 0) (by omega) (hRowBounds 0 (by omega)).1
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
  have hCoverPositive :=
    fourMaskCoverCount_pos_of_activeSupportsCovered m hActive hCovered
  have hCoverUpper := (fourMaskCoverCount_le_weightedCoverCount m).trans hWeighted
  have hPairUpper :=
    (middleFourMaskPairCoverCount_le_pairCoverCount m).trans hPair
  have hMaskClutter :=
    fourMaskRowsClutter_multiplicityMask_of_rowsClutter m hClutter
  have hCoveredUnion :=
    fourMaskCoveredUnion_multiplicityMask_of_activeSupportsCovered m hCovered
  unfold smallFourMaskValid
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true hCoveredUnion⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true hPairUpper⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, decide_eq_true ⟨hCoverPositive, hCoverUpper⟩⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hMaskClutter⟩
  apply Bool.and_eq_true_iff.mpr
  exact ⟨decide_eq_true hMaskNonzero, hMaskDegreeAll⟩

def fourExceptionalMultiplicityCertificate : List (List Nat) :=
  [
    [0, 0, 0, 1, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 2, 0, 1, 1, 1, 0, 0, 0, 0],
    [0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0],
    [0, 0, 1, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0],
    [0, 0, 1, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0]
  ]

def fourExceptionalMultiplicityInCertificate (m : FourMultiplicity) : Bool :=
  fourExceptionalMultiplicityCertificate.any fun values ↦ decide (m.toList = values)

def fourExceptionalMultiplicityLeafValid (m : FourMultiplicity) : Bool :=
  decide (fourRowDegree m 0 = 2) &&
    ([1, 2, 3].all fun row ↦
      decide (3 ≤ fourRowDegree m row ∧ fourRowDegree m row ≤ 5))

def threePaddedMultiplicityCertificate : List (List Nat) :=
  [
    [1, 0, 0, 1, 0, 1, 0, 1, 0, 2, 0, 0, 0, 0],
    [1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0],
    [1, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0],
    [1, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 1, 0, 0],
    [1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0],
    [1, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0],
    [1, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 0, 0],
    [1, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1, 0, 0],
    [1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0],
    [1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0]
  ]

def threePaddedMultiplicityInCertificate (m : FourMultiplicity) : Bool :=
  threePaddedMultiplicityCertificate.any fun values ↦ decide (m.toList = values)

def threePaddedMultiplicityLeafValid (m : FourMultiplicity) : Bool :=
  decide (fourRowDegree m 0 = 1) &&
    ([1, 2, 3].all fun row ↦
      decide (2 ≤ fourRowDegree m row ∧ fourRowDegree m row ≤ 5)) &&
        decide (([1, 2, 3].filter fun row ↦ fourRowDegree m row = 2).length ≤ 1)

def FourExceptionalModelProperty (values : List Nat) : Prop :=
  let B := middleFourModelBlocker values
  B.card = 5 ∧
    ∀ P ∈ B, ∀ Q ∈ B,
      3 ≤ P.card → 3 ≤ Q.card → P ≠ Q → (P ∩ Q).card = 2

def ThreePaddedModelProperty (values : List Nat) : Prop :=
  let B := middleFourModelBlocker values
  B.card = 5 ∧ ∀ P ∈ B, P.card = 3

end AiMathLab.P0054.G420
