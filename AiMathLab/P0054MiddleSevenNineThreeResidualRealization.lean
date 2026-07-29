import AiMathLab.P0054MiddleSevenNineThreeResidualSound

/-!
# Realizing a three-row residual profile by actual points
-/

namespace AiMathLab.P0054.MiddleSevenNineThreeResidualRealization

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.MiddleSevenNineThreeResidualFinite
open AiMathLab.P0054.MiddleSevenNineThreeResidualSound

def threeRowMultiplicityValues {alpha : Type*} [DecidableEq alpha]
    (A B C : Row alpha) : List Nat :=
  threeResidualMultiplicityValues
    (privatePart A B C).card
    (privatePart B A C).card
    (privatePart C A B).card
    (sharedPart A B C).card
    (sharedPart A C B).card
    (sharedPart B C A).card

theorem threePermuteMultiplicityValues_012
    (p q x12 r x13 x23 : Nat) :
    threePermuteMultiplicityValues [0, 1, 2]
        [p, q, x12, r, x13, x23] =
      [p, q, x12, r, x13, x23] := by
  rfl

theorem threePermuteMultiplicityValues_021
    (p q x12 r x13 x23 : Nat) :
    threePermuteMultiplicityValues [0, 2, 1]
        [p, q, x12, r, x13, x23] =
      [p, r, x13, q, x12, x23] := by
  rfl

theorem threePermuteMultiplicityValues_102
    (p q x12 r x13 x23 : Nat) :
    threePermuteMultiplicityValues [1, 0, 2]
        [p, q, x12, r, x13, x23] =
      [q, p, x12, r, x23, x13] := by
  rfl

theorem threePermuteMultiplicityValues_120
    (p q x12 r x13 x23 : Nat) :
    threePermuteMultiplicityValues [1, 2, 0]
        [p, q, x12, r, x13, x23] =
      [r, p, x13, q, x23, x12] := by
  rfl

theorem threePermuteMultiplicityValues_201
    (p q x12 r x13 x23 : Nat) :
    threePermuteMultiplicityValues [2, 0, 1]
        [p, q, x12, r, x13, x23] =
      [q, r, x23, p, x12, x13] := by
  rfl

theorem threePermuteMultiplicityValues_210
    (p q x12 r x13 x23 : Nat) :
    threePermuteMultiplicityValues [2, 1, 0]
        [p, q, x12, r, x13, x23] =
      [r, q, x23, p, x13, x12] := by
  rfl

noncomputable def threeOrderedPointList
    {alpha : Type*} [DecidableEq alpha]
    (A B C : Row alpha) : List alpha :=
  (privatePart A B C).toList ++
    (privatePart B A C).toList ++
    (sharedPart A B C).toList ++
    (privatePart C A B).toList ++
    (sharedPart A C B).toList ++
    (sharedPart B C A).toList

theorem map_finset_toList_eq_replicate_of_constant
    {alpha beta : Type*} [DecidableEq alpha]
    {S : Finset alpha} {f : alpha → beta} {value : beta}
    (hConstant : ∀ point ∈ S, f point = value) :
    S.toList.map f = List.replicate S.card value := by
  have hMap :
      S.toList.map f = List.replicate (S.toList.map f).length value := by
    apply (List.eq_replicate_length).2
    intro output hOutput
    obtain ⟨point, hPoint, rfl⟩ := List.mem_map.mp hOutput
    exact hConstant point (Finset.mem_toList.mp hPoint)
  simpa only [List.length_map, Finset.length_toList] using hMap

theorem threeOrderedPointList_supports
    {alpha : Type*} [DecidableEq alpha]
    (A B C : Row alpha) :
    (threeOrderedPointList A B C).map (threeSupportMask A B C) =
      threeMultiplicitySupportList (threeRowMultiplicityValues A B C) := by
  classical
  unfold threeOrderedPointList threeRowMultiplicityValues
    threeMultiplicitySupportList threeResidualMultiplicityValues
  simp only [List.map_append]
  rw [map_finset_toList_eq_replicate_of_constant
      (fun point hPoint ↦ threeSupportMask_privatePart_first hPoint),
    map_finset_toList_eq_replicate_of_constant
      (fun point hPoint ↦ threeSupportMask_privatePart_second hPoint),
    map_finset_toList_eq_replicate_of_constant
      (fun point hPoint ↦ threeSupportMask_sharedPart_twelve hPoint),
    map_finset_toList_eq_replicate_of_constant
      (fun point hPoint ↦ threeSupportMask_privatePart_third hPoint),
    map_finset_toList_eq_replicate_of_constant
      (fun point hPoint ↦ threeSupportMask_sharedPart_thirteen hPoint),
    map_finset_toList_eq_replicate_of_constant
      (fun point hPoint ↦ threeSupportMask_sharedPart_twentyThree hPoint)]
  rfl

theorem threeOrderedPointList_nodup
    {alpha : Type*} [DecidableEq alpha]
    (A B C : Row alpha) :
    (threeOrderedPointList A B C).Nodup := by
  classical
  let P := privatePart A B C
  let Q := privatePart B A C
  let X := sharedPart A B C
  let R := privatePart C A B
  let Y := sharedPart A C B
  let Z := sharedPart B C A
  have hPCode : ∀ point ∈ P.toList, threeSupportMask A B C point = 1 := by
    intro point hPoint
    exact threeSupportMask_privatePart_first
      (Finset.mem_toList.mp (by simpa [P] using hPoint))
  have hQCode : ∀ point ∈ Q.toList, threeSupportMask A B C point = 2 := by
    intro point hPoint
    exact threeSupportMask_privatePart_second
      (Finset.mem_toList.mp (by simpa [Q] using hPoint))
  have hXCode : ∀ point ∈ X.toList, threeSupportMask A B C point = 3 := by
    intro point hPoint
    exact threeSupportMask_sharedPart_twelve
      (Finset.mem_toList.mp (by simpa [X] using hPoint))
  have hRCode : ∀ point ∈ R.toList, threeSupportMask A B C point = 4 := by
    intro point hPoint
    exact threeSupportMask_privatePart_third
      (Finset.mem_toList.mp (by simpa [R] using hPoint))
  have hYCode : ∀ point ∈ Y.toList, threeSupportMask A B C point = 5 := by
    intro point hPoint
    exact threeSupportMask_sharedPart_thirteen
      (Finset.mem_toList.mp (by simpa [Y] using hPoint))
  have hZCode : ∀ point ∈ Z.toList, threeSupportMask A B C point = 6 := by
    intro point hPoint
    exact threeSupportMask_sharedPart_twentyThree
      (Finset.mem_toList.mp (by simpa [Z] using hPoint))
  have hYZDisjoint : List.Disjoint Y.toList Z.toList := by
    apply List.disjoint_left.mpr
    intro point hPointY hPointZ
    have hY := hYCode point hPointY
    have hZ := hZCode point hPointZ
    omega
  have hYZNodup : (Y.toList ++ Z.toList).Nodup :=
    (Finset.nodup_toList Y).append (Finset.nodup_toList Z) hYZDisjoint
  have hR_YZ_Disjoint : List.Disjoint R.toList (Y.toList ++ Z.toList) := by
    apply List.disjoint_left.mpr
    intro point hPointR hPointYZ
    simp only [List.mem_append] at hPointYZ
    rcases hPointYZ with hPointY | hPointZ
    · have hR := hRCode point hPointR
      have hY := hYCode point hPointY
      omega
    · have hR := hRCode point hPointR
      have hZ := hZCode point hPointZ
      omega
  have hRYZNodup : (R.toList ++ Y.toList ++ Z.toList).Nodup :=
    by
      simpa [List.append_assoc] using
        (Finset.nodup_toList R).append hYZNodup hR_YZ_Disjoint
  have hX_RYZ_Disjoint :
      List.Disjoint X.toList (R.toList ++ Y.toList ++ Z.toList) := by
    apply List.disjoint_left.mpr
    intro point hPointX hPointRYZ
    have hMembers :
        point ∈ R.toList ∨ point ∈ Y.toList ∨ point ∈ Z.toList := by
      simpa [List.mem_append, or_assoc] using hPointRYZ
    rcases hMembers with hPointR | hPointY | hPointZ
    · have hX := hXCode point hPointX
      have hR := hRCode point hPointR
      omega
    · have hX := hXCode point hPointX
      have hY := hYCode point hPointY
      omega
    · have hX := hXCode point hPointX
      have hZ := hZCode point hPointZ
      omega
  have hXRYZNodup :
      (X.toList ++ R.toList ++ Y.toList ++ Z.toList).Nodup :=
    by
      simpa [List.append_assoc] using
        (Finset.nodup_toList X).append hRYZNodup hX_RYZ_Disjoint
  have hQ_XRYZ_Disjoint :
      List.Disjoint Q.toList
        (X.toList ++ R.toList ++ Y.toList ++ Z.toList) := by
    apply List.disjoint_left.mpr
    intro point hPointQ hPointXRYZ
    have hMembers :
        point ∈ X.toList ∨ point ∈ R.toList ∨
          point ∈ Y.toList ∨ point ∈ Z.toList := by
      simpa [List.mem_append, or_assoc] using hPointXRYZ
    rcases hMembers with hPointX | hPointR | hPointY | hPointZ
    · have hQ := hQCode point hPointQ
      have hX := hXCode point hPointX
      omega
    · have hQ := hQCode point hPointQ
      have hR := hRCode point hPointR
      omega
    · have hQ := hQCode point hPointQ
      have hY := hYCode point hPointY
      omega
    · have hQ := hQCode point hPointQ
      have hZ := hZCode point hPointZ
      omega
  have hQXRYZNodup :
      (Q.toList ++ X.toList ++ R.toList ++ Y.toList ++ Z.toList).Nodup :=
    by
      simpa [List.append_assoc] using
        (Finset.nodup_toList Q).append hXRYZNodup hQ_XRYZ_Disjoint
  have hP_QXRYZ_Disjoint :
      List.Disjoint P.toList
        (Q.toList ++ X.toList ++ R.toList ++ Y.toList ++ Z.toList) := by
    apply List.disjoint_left.mpr
    intro point hPointP hPointQXRYZ
    have hMembers :
        point ∈ Q.toList ∨ point ∈ X.toList ∨ point ∈ R.toList ∨
          point ∈ Y.toList ∨ point ∈ Z.toList := by
      simpa [List.mem_append, or_assoc] using hPointQXRYZ
    rcases hMembers with hPointQ | hPointX | hPointR | hPointY | hPointZ
    · have hP := hPCode point hPointP
      have hQ := hQCode point hPointQ
      omega
    · have hP := hPCode point hPointP
      have hX := hXCode point hPointX
      omega
    · have hP := hPCode point hPointP
      have hR := hRCode point hPointR
      omega
    · have hP := hPCode point hPointP
      have hY := hYCode point hPointY
      omega
    · have hP := hPCode point hPointP
      have hZ := hZCode point hPointZ
      omega
  change (P.toList ++ Q.toList ++ X.toList ++ R.toList ++
    Y.toList ++ Z.toList).Nodup
  simpa [List.append_assoc] using
    (Finset.nodup_toList P).append hQXRYZNodup hP_QXRYZ_Disjoint

theorem mem_threeOrderedPointList_iff
    {alpha : Type*} [DecidableEq alpha]
    {A B C : Row alpha}
    (hNoCommon : ∀ point, ¬(point ∈ A ∧ point ∈ B ∧ point ∈ C))
    (point : alpha) :
    point ∈ threeOrderedPointList A B C ↔
      point ∈ A ∨ point ∈ B ∨ point ∈ C := by
  classical
  by_cases hA : point ∈ A <;>
    by_cases hB : point ∈ B <;>
    by_cases hC : point ∈ C <;>
    simp_all [threeOrderedPointList, privatePart, sharedPart]

theorem threeOrderedPointList_toFinset
    {alpha : Type*} [DecidableEq alpha]
    {A B C : Row alpha}
    (hNoCommon : ∀ point, ¬(point ∈ A ∧ point ∈ B ∧ point ∈ C)) :
    (threeOrderedPointList A B C).toFinset = A ∪ B ∪ C := by
  classical
  ext point
  simp [mem_threeOrderedPointList_iff hNoCommon point]

theorem three_rows_pairwise_ne_of_card_eq_three
    {alpha : Type*} [DecidableEq alpha]
    {A B C : Row alpha}
    (hRowsCard : ({A, B, C} : G413.Hypergraph alpha).card = 3) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  have pair_card_le_two (X Y : Row alpha) :
      ({X, Y} : G413.Hypergraph alpha).card ≤ 2 := by
    calc
      ({X, Y} : G413.Hypergraph alpha).card ≤
          ({Y} : G413.Hypergraph alpha).card + 1 :=
        Finset.card_insert_le X {Y}
      _ = 2 := by simp
  have hAB : A ≠ B := by
    intro hEqual
    subst B
    have hDuplicate :
        ({A, A, C} : G413.Hypergraph alpha) = {A, C} := by
      ext R
      simp
    have hLe : ({A, A, C} : G413.Hypergraph alpha).card ≤ 2 := by
      rw [hDuplicate]
      exact pair_card_le_two A C
    omega
  have hAC : A ≠ C := by
    intro hEqual
    subst C
    have hDuplicate :
        ({A, B, A} : G413.Hypergraph alpha) = {A, B} := by
      ext R
      simp [or_comm, or_left_comm]
    have hLe : ({A, B, A} : G413.Hypergraph alpha).card ≤ 2 := by
      rw [hDuplicate]
      exact pair_card_le_two A B
    omega
  have hBC : B ≠ C := by
    intro hEqual
    subst C
    have hDuplicate :
        ({A, B, B} : G413.Hypergraph alpha) = {A, B} := by
      ext R
      simp
    have hLe : ({A, B, B} : G413.Hypergraph alpha).card ≤ 2 := by
      rw [hDuplicate]
      exact pair_card_le_two A B
    omega
  exact ⟨hAB, hAC, hBC⟩

theorem threeMaskRank_supportMask_eq_degree
    {alpha : Type*} [DecidableEq alpha]
    {H : G413.Hypergraph alpha} {A B C : Row alpha}
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hH : H = {A, B, C}) (point : alpha) :
    AiMathLab.P0054.MiddleSevenNineSixCouplingFinite.threeMaskRank
        (threeSupportMask A B C point) =
      degree H point := by
  by_cases hA : point ∈ A <;>
    by_cases hB : point ∈ B <;>
    by_cases hC : point ∈ C <;>
    simp [AiMathLab.P0054.MiddleSevenNineSixCouplingFinite.threeMaskRank,
      threeSupportMask, degree, hH, Finset.filter_insert,
      Finset.filter_singleton, hAB, hAC, hBC, hA, hB, hC] <;>
    decide

theorem permuted_multiplicity_realized_by_row_reordering
    {alpha : Type*} [DecidableEq alpha]
    {A B C : Row alpha} {permutation representative : List Nat}
    (hPermutation : permutation ∈ threeRowPermutations)
    (hValues :
      threePermuteMultiplicityValues permutation
          (threeRowMultiplicityValues A B C) = representative) :
    ∃ A' B' C',
      ({A', B', C'} : G413.Hypergraph alpha) = {A, B, C} ∧
      threeRowMultiplicityValues A' B' C' = representative := by
  simp only [threeRowPermutations, List.mem_cons, List.not_mem_nil, or_false]
    at hPermutation
  rcases hPermutation with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨A, B, C, rfl, ?_⟩
    simpa only [threeRowMultiplicityValues, threeResidualMultiplicityValues,
      threePermuteMultiplicityValues_012] using hValues
  · refine ⟨A, C, B, ?_, ?_⟩
    · ext R
      simp [or_comm, or_left_comm]
    · simpa [threeRowMultiplicityValues, threeResidualMultiplicityValues,
        threePermuteMultiplicityValues_021,
        privatePart, sharedPart, Finset.union_comm, Finset.inter_comm] using hValues
  · refine ⟨B, A, C, ?_, ?_⟩
    · ext R
      simp [or_comm, or_left_comm]
    · simpa [threeRowMultiplicityValues, threeResidualMultiplicityValues,
        threePermuteMultiplicityValues_102,
        privatePart, sharedPart, Finset.union_comm, Finset.inter_comm] using hValues
  · refine ⟨C, A, B, ?_, ?_⟩
    · ext R
      simp [or_comm, or_left_comm]
    · simpa [threeRowMultiplicityValues, threeResidualMultiplicityValues,
        threePermuteMultiplicityValues_120,
        privatePart, sharedPart, Finset.union_comm, Finset.inter_comm] using hValues
  · refine ⟨B, C, A, ?_, ?_⟩
    · ext R
      simp [or_comm, or_left_comm]
    · simpa [threeRowMultiplicityValues, threeResidualMultiplicityValues,
        threePermuteMultiplicityValues_201,
        privatePart, sharedPart, Finset.union_comm, Finset.inter_comm] using hValues
  · refine ⟨C, B, A, ?_, ?_⟩
    · ext R
      simp [or_comm, or_left_comm]
    · simpa [threeRowMultiplicityValues, threeResidualMultiplicityValues,
        threePermuteMultiplicityValues_210,
        privatePart, sharedPart, Finset.union_comm, Finset.inter_comm] using hValues

theorem accepted_realized_by_ordered_point_list
    {alpha : Type*} [DecidableEq alpha]
    {A B C : Row alpha} {p q r x12 x13 x23 : Nat}
    (hp : p = (privatePart A B C).card)
    (hq : q = (privatePart B A C).card)
    (hr : r = (privatePart C A B).card)
    (hx12 : x12 = (sharedPart A B C).card)
    (hx13 : x13 = (sharedPart A C B).card)
    (hx23 : x23 = (sharedPart B C A).card)
    (hAccepted :
      threeResidualMarginalAccepted p q r x12 x13 x23 = true) :
    ∃ A' B' C' index,
      index < 6 ∧
        ({A', B', C'} : G413.Hypergraph alpha) = {A, B, C} ∧
      (threeOrderedPointList A' B' C').map
          (threeSupportMask A' B' C') =
        AiMathLab.P0054.MiddleSevenNineSixCouplingFinite.sixResidualProfile index := by
  obtain ⟨representative, _hRepresentative, permutation, hPermutation,
      index, hIndex, hValues, hProfile⟩ :=
    accepted_has_residual_profile hAccepted
  have hValues' :
      threePermuteMultiplicityValues permutation
          (threeRowMultiplicityValues A B C) = representative := by
    simpa [threeRowMultiplicityValues, hp, hq, hr, hx12, hx13, hx23] using hValues
  obtain ⟨A', B', C', hRows, hReordered⟩ :=
    permuted_multiplicity_realized_by_row_reordering hPermutation hValues'
  refine ⟨A', B', C', index, hIndex, hRows, ?_⟩
  rw [threeOrderedPointList_supports, hReordered, hProfile]

theorem threeRow_residual_actual_profile
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 3)
    (hHRowsLower : RowsCardAtLeast H 2)
    (hHRowsUpper : ∀ R ∈ H, R.card ≤ 5)
    (hNoCommon : ∀ point, ∃ R ∈ H, point ∉ R)
    (hBlockerUpper : (blocker H).card ≤ 4) :
    ∃ (A B C : Row alpha) (index : Nat) (points : List alpha),
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ H = {A, B, C} ∧
      index < 6 ∧ points.Nodup ∧
      (∀ point, point ∈ points ↔ ∃ R ∈ H, point ∈ R) ∧
      points.map (threeSupportMask A B C) =
        AiMathLab.P0054.MiddleSevenNineSixCouplingFinite.sixResidualProfile index := by
  classical
  obtain ⟨A0, B0, C0, _hA0B0, _hA0C0, _hB0C0, hH, hAccepted⟩ :=
    threeRow_residual_marginal_accepted hHClutter hHCard
      hHRowsLower hHRowsUpper hNoCommon hBlockerUpper
  obtain ⟨A, B, C, index, hIndex, hRows, hSupports⟩ :=
    accepted_realized_by_ordered_point_list
      (A := A0) (B := B0) (C := C0)
      rfl rfl rfl rfl rfl rfl hAccepted
  have hHReordered : H = {A, B, C} := hH.trans hRows.symm
  have hRowsCard : ({A, B, C} : G413.Hypergraph alpha).card = 3 :=
    (congrArg Finset.card hHReordered.symm).trans hHCard
  obtain ⟨hAB, hAC, hBC⟩ :=
    three_rows_pairwise_ne_of_card_eq_three hRowsCard
  have hNoCommonABC :
      ∀ point, ¬(point ∈ A ∧ point ∈ B ∧ point ∈ C) := by
    intro point hPoint
    obtain ⟨R, hRH, hPointR⟩ := hNoCommon point
    rw [hHReordered] at hRH
    simp only [Finset.mem_insert, Finset.mem_singleton] at hRH
    rcases hRH with rfl | rfl | rfl
    · exact hPointR hPoint.1
    · exact hPointR hPoint.2.1
    · exact hPointR hPoint.2.2
  have hPoints :
      ∀ point, point ∈ threeOrderedPointList A B C ↔
        ∃ R ∈ H, point ∈ R := by
    intro point
    rw [mem_threeOrderedPointList_iff hNoCommonABC point]
    constructor
    · intro hPoint
      rcases hPoint with hPointA | hPointB | hPointC
      · exact ⟨A, by simp [hHReordered], hPointA⟩
      · exact ⟨B, by simp [hHReordered], hPointB⟩
      · exact ⟨C, by simp [hHReordered], hPointC⟩
    · rintro ⟨R, hRH, hPointR⟩
      rw [hHReordered] at hRH
      simp only [Finset.mem_insert, Finset.mem_singleton] at hRH
      rcases hRH with rfl | rfl | rfl
      · exact Or.inl hPointR
      · exact Or.inr (Or.inl hPointR)
      · exact Or.inr (Or.inr hPointR)
  exact ⟨A, B, C, index, threeOrderedPointList A B C,
    hAB, hAC, hBC, hHReordered, hIndex,
    threeOrderedPointList_nodup A B C, hPoints, hSupports⟩

end AiMathLab.P0054.MiddleSevenNineThreeResidualRealization
