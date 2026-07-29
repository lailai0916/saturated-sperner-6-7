import AiMathLab.P0054G413.PairEndpoint

namespace AiMathLab.P0054.G413

def pointSupport {α : Type*} [DecidableEq α]
    (K : Hypergraph α) (x : α) : Hypergraph α :=
  K.filter fun E ↦ x ∈ E

@[simp]
theorem mem_pointSupport {α : Type*} [DecidableEq α]
    {K : Hypergraph α} {x : α} {E : Row α} :
    E ∈ pointSupport K x ↔ E ∈ K ∧ x ∈ E := by
  simp [pointSupport]

theorem pointSupport_card {α : Type*} [DecidableEq α]
    (K : Hypergraph α) (x : α) :
    (pointSupport K x).card = degree K x := by
  rfl

theorem pair_blocker_support_union {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y : α}
    (hPair : ({x, y} : Row α) ∈ blocker K) :
    pointSupport K x ∪ pointSupport K y = K := by
  ext E
  constructor
  · intro hE
    rcases Finset.mem_union.mp hE with hx | hy
    · exact (mem_pointSupport.mp hx).1
    · exact (mem_pointSupport.mp hy).1
  · intro hE
    obtain ⟨z, hzPair, hzE⟩ := (mem_blocker.mp hPair).prop E hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
    rcases hzPair with rfl | rfl
    · exact Finset.mem_union_left _ (mem_pointSupport.mpr ⟨hE, hzE⟩)
    · exact Finset.mem_union_right _ (mem_pointSupport.mpr ⟨hE, hzE⟩)

theorem pair_blocker_support_private {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y : α}
    (hPair : ({x, y} : Row α) ∈ blocker K)
    (hxy : x ≠ y) :
    (pointSupport K x \ pointSupport K y).Nonempty ∧
      (pointSupport K y \ pointSupport K x).Nonempty := by
  have hMin := mem_blocker.mp hPair
  have hxPair : x ∈ ({x, y} : Row α) := by simp
  have hyPair : y ∈ ({x, y} : Row α) := by simp
  obtain ⟨E, hEPrivate⟩ := hMin.exists_privateRow hxPair
  obtain ⟨F, hFPrivate⟩ := hMin.exists_privateRow hyPair
  have hyE : y ∉ E := by
    intro hyE
    exact hxy ((hEPrivate.2.2.2 hyPair hyE).symm)
  have hxF : x ∉ F := by
    intro hxF
    exact hxy (hFPrivate.2.2.2 hxPair hxF)
  constructor
  · exact ⟨E, Finset.mem_sdiff.mpr
      ⟨mem_pointSupport.mpr ⟨hEPrivate.1, hEPrivate.2.2.1⟩,
        fun h ↦ hyE (mem_pointSupport.mp h).2⟩⟩
  · exact ⟨F, Finset.mem_sdiff.mpr
      ⟨mem_pointSupport.mpr ⟨hFPrivate.1, hFPrivate.2.2.1⟩,
        fun h ↦ hxF (mem_pointSupport.mp h).2⟩⟩

theorem pair_blocker_support_type {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y : α}
    (hKcard : K.card = 5)
    (hDegree : MaxDegreeAtMost K 3)
    (hPair : ({x, y} : Row α) ∈ blocker K)
    (hxy : x ≠ y) :
    ((pointSupport K x).card = 2 ∧ (pointSupport K y).card = 3 ∧
        Disjoint (pointSupport K x) (pointSupport K y)) ∨
      ((pointSupport K x).card = 3 ∧ (pointSupport K y).card = 2 ∧
        Disjoint (pointSupport K x) (pointSupport K y)) ∨
      ((pointSupport K x).card = 3 ∧ (pointSupport K y).card = 3 ∧
        (pointSupport K x ∩ pointSupport K y).card = 1) := by
  let X := pointSupport K x
  let Y := pointSupport K y
  have hUnion : X ∪ Y = K := pair_blocker_support_union hPair
  obtain ⟨hXPrivate, hYPrivate⟩ := pair_blocker_support_private hPair hxy
  have hXpositive : 0 < X.card := by
    obtain ⟨E, hE⟩ := hXPrivate
    exact Finset.card_pos.mpr ⟨E, (Finset.mem_sdiff.mp hE).1⟩
  have hYpositive : 0 < Y.card := by
    obtain ⟨E, hE⟩ := hYPrivate
    exact Finset.card_pos.mpr ⟨E, (Finset.mem_sdiff.mp hE).1⟩
  have hXupper : X.card ≤ 3 := by simpa [X, pointSupport_card] using hDegree x
  have hYupper : Y.card ≤ 3 := by simpa [Y, pointSupport_card] using hDegree y
  have hCardUnion : (X ∪ Y).card = 5 := by rw [hUnion, hKcard]
  have hCardFormula := Finset.card_union_add_card_inter X Y
  rw [hCardUnion] at hCardFormula
  have hInterUpper : (X ∩ Y).card ≤ 1 := by omega
  by_cases hInterEmpty : (X ∩ Y).card = 0
  · have hDisjoint : Disjoint X Y := by
      rw [Finset.disjoint_iff_inter_eq_empty, Finset.card_eq_zero.mp hInterEmpty]
    have hSum : X.card + Y.card = 5 := by omega
    rcases (show X.card = 2 ∨ X.card = 3 by omega) with hX | hX
    · exact Or.inl (by simpa [X, Y] using (show
        X.card = 2 ∧ Y.card = 3 ∧ Disjoint X Y from ⟨hX, by omega, hDisjoint⟩))
    · exact Or.inr (Or.inl (by simpa [X, Y] using (show
        X.card = 3 ∧ Y.card = 2 ∧ Disjoint X Y from ⟨hX, by omega, hDisjoint⟩)))
  · have hInterOne : (X ∩ Y).card = 1 := by omega
    exact Or.inr (Or.inr (by simpa [X, Y] using (show
      X.card = 3 ∧ Y.card = 3 ∧ (X ∩ Y).card = 1 from
        ⟨by omega, by omega, hInterOne⟩)))

theorem exists_row_avoiding_nonblocker_pair {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y : α}
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hNotPair : ({x, y} : Row α) ∉ blocker K) :
    ∃ E ∈ K, x ∉ E ∧ y ∉ E := by
  have hNotTransversal : ¬ IsTransversal K ({x, y} : Row α) := by
    intro hTransversal
    obtain ⟨T, hTPair, hTmin⟩ := exists_minimalTransversal_subset hTransversal
    have hTb : T ∈ blocker K := mem_blocker.mpr hTmin
    have hTlower : 2 ≤ T.card := hBRows T hTb
    have hTupper : T.card ≤ ({x, y} : Row α).card := Finset.card_le_card hTPair
    have hPairUpper : ({x, y} : Row α).card ≤ 2 := Finset.card_le_two
    have hCardEq : T.card = ({x, y} : Row α).card := by omega
    have hEq : T = {x, y} := Finset.eq_of_subset_of_card_le hTPair (by omega)
    exact hNotPair (hEq ▸ hTb)
  simp only [IsTransversal] at hNotTransversal
  push Not at hNotTransversal
  obtain ⟨E, hEK, hNoHit⟩ := hNotTransversal
  refine ⟨E, hEK, ?_, ?_⟩
  · intro hxE
    exact hNoHit x (by simp) hxE
  · intro hyE
    exact hNoHit y (by simp) hyE

end AiMathLab.P0054.G413
