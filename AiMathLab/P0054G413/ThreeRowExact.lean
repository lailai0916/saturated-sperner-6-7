import AiMathLab.P0054G413.ThreeRows

namespace AiMathLab.P0054.G413

def privatePart {α : Type*} [DecidableEq α]
    (A B C : Row α) : Row α :=
  A \ (B ∪ C)

def sharedPart {α : Type*} [DecidableEq α]
    (A B C : Row α) : Row α :=
  (A ∩ B) \ C

noncomputable def tripleChoiceRows {α : Type*} [DecidableEq α]
    (A B C : Row α) : Hypergraph α := by
  classical
  exact ((A.product B).product C).image fun x ↦ {x.1.1, x.1.2, x.2}

def rowsCardExactly {α : Type*}
    (H : Hypergraph α) (n : Nat) : Hypergraph α :=
  H.filter fun E ↦ E.card = n

@[simp]
theorem mem_rowsCardExactly {α : Type*} {H : Hypergraph α} {n : Nat} {E : Row α} :
    E ∈ rowsCardExactly H n ↔ E ∈ H ∧ E.card = n := by
  simp [rowsCardExactly]

@[simp]
theorem mem_tripleChoiceRows {α : Type*} [DecidableEq α]
    {A B C T : Row α} :
    T ∈ tripleChoiceRows A B C ↔
      ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, {a, b, c} = T := by
  classical
  constructor
  · intro hT
    obtain ⟨x, hx, hxT⟩ := Finset.mem_image.mp hT
    obtain ⟨hxPair, hxc⟩ := Finset.mem_product.mp hx
    obtain ⟨hxa, hxb⟩ := Finset.mem_product.mp hxPair
    exact ⟨x.1.1, hxa, x.1.2, hxb, x.2, hxc, hxT⟩
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    exact Finset.mem_image.mpr
      ⟨((a, b), c), Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩, rfl⟩

theorem privatePart_pairwise_disjoint {α : Type*} [DecidableEq α]
    (T₁ T₂ T₃ : Row α) :
    Disjoint (privatePart T₁ T₂ T₃) (privatePart T₂ T₁ T₃) ∧
      Disjoint (privatePart T₁ T₂ T₃) (privatePart T₃ T₁ T₂) ∧
      Disjoint (privatePart T₂ T₁ T₃) (privatePart T₃ T₁ T₂) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    exact (Finset.mem_sdiff.mp hx₁).2
      (Finset.mem_union_left _ (Finset.mem_sdiff.mp hx₂).1)
  constructor
  · apply Finset.disjoint_left.mpr
    intro x hx₁ hx₃
    exact (Finset.mem_sdiff.mp hx₁).2
      (Finset.mem_union_right _ (Finset.mem_sdiff.mp hx₃).1)
  · apply Finset.disjoint_left.mpr
    intro x hx₂ hx₃
    exact (Finset.mem_sdiff.mp hx₂).2
      (Finset.mem_union_right _ (Finset.mem_sdiff.mp hx₃).1)

theorem tripleChoiceRows_card {α : Type*} [DecidableEq α]
    {A B C : Row α}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (tripleChoiceRows A B C).card = A.card * B.card * C.card := by
  classical
  let choices := (A.product B).product C
  let row : (α × α) × α → Row α := fun x ↦ {x.1.1, x.1.2, x.2}
  have hInjective : Set.InjOn row (↑choices : Set ((α × α) × α)) := by
    intro x hx y hy hEq
    have hx' : x ∈ choices := hx
    have hy' : y ∈ choices := hy
    obtain ⟨hxPair, hxC⟩ := Finset.mem_product.mp hx'
    obtain ⟨hxA, hxB⟩ := Finset.mem_product.mp hxPair
    obtain ⟨hyPair, hyC⟩ := Finset.mem_product.mp hy'
    obtain ⟨hyA, hyB⟩ := Finset.mem_product.mp hyPair
    apply Prod.ext
    · apply Prod.ext
      · have hxMem : x.1.1 ∈ row y := by rw [← hEq]; simp [row]
        simp only [row, Finset.mem_insert, Finset.mem_singleton] at hxMem
        rcases hxMem with hxy | hxy | hxy
        · exact hxy
        · exact (Finset.disjoint_left.mp hAB hxA (hxy ▸ hyB)).elim
        · exact (Finset.disjoint_left.mp hAC hxA (hxy ▸ hyC)).elim
      · have hxMem : x.1.2 ∈ row y := by rw [← hEq]; simp [row]
        simp only [row, Finset.mem_insert, Finset.mem_singleton] at hxMem
        rcases hxMem with hxy | hxy | hxy
        · exact (Finset.disjoint_left.mp hAB (hxy ▸ hyA) hxB).elim
        · exact hxy
        · exact (Finset.disjoint_left.mp hBC hxB (hxy ▸ hyC)).elim
    · have hxMem : x.2 ∈ row y := by rw [← hEq]; simp [row]
      simp only [row, Finset.mem_insert, Finset.mem_singleton] at hxMem
      rcases hxMem with hxy | hxy | hxy
      · exact (Finset.disjoint_left.mp hAC (hxy ▸ hyA) hxC).elim
      · exact (Finset.disjoint_left.mp hBC (hxy ▸ hyB) hxC).elim
      · exact hxy
  calc
    (tripleChoiceRows A B C).card = (choices.image row).card := by
      rfl
    _ = choices.card := Finset.card_image_iff.mpr hInjective
    _ = A.card * B.card * C.card := by simp [choices, Finset.card_product]

theorem pair_mem_blocker_threeRows {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {x y : α}
    (hTransversal : IsTransversal K {x, y})
    (hxPrivate : ∃ E ∈ K, x ∈ E ∧ y ∉ E)
    (hyPrivate : ∃ E ∈ K, y ∈ E ∧ x ∉ E) :
    ({x, y} : Row α) ∈ blocker K := by
  apply mem_blocker.mpr
  apply hTransversal.minimal_of_privateRows
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · obtain ⟨E, hEK, hxE, hyE⟩ := hxPrivate
    exact ⟨E, hEK, by simp, hxE, by
      intro z hzPair hzE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
      rcases hzPair with rfl | rfl
      · rfl
      · exact (hyE hzE).elim⟩
  · obtain ⟨E, hEK, hyE, hxE⟩ := hyPrivate
    exact ⟨E, hEK, by simp, hyE, by
      intro z hzPair hzE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzPair
      rcases hzPair with rfl | rfl
      · exact (hxE hzE).elim
      · rfl⟩

theorem shared_private_pair_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α} {u c : α}
    (hK : K = {T₁, T₂, T₃})
    (hu : u ∈ sharedPart T₁ T₂ T₃)
    (hc : c ∈ privatePart T₃ T₁ T₂) :
    ({u, c} : Row α) ∈ blocker K := by
  have huT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hu).1).1
  have huT₂ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hu).1).2
  have huT₃ := (Finset.mem_sdiff.mp hu).2
  have hcT₃ := (Finset.mem_sdiff.mp hc).1
  have hcT₁ : c ∉ T₁ := fun hcT₁ ↦
    (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_left _ hcT₁)
  have hcT₂ : c ∉ T₂ := fun hcT₂ ↦
    (Finset.mem_sdiff.mp hc).2 (Finset.mem_union_right _ hcT₂)
  apply pair_mem_blocker_threeRows
  · intro T hT
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · exact ⟨u, by simp, huT₁⟩
    · exact ⟨u, by simp, huT₂⟩
    · exact ⟨c, by simp, hcT₃⟩
  · exact ⟨T₁, by simp [hK], huT₁, hcT₁⟩
  · exact ⟨T₃, by simp [hK], hcT₃, huT₃⟩

theorem shared_shared_pair_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α} {u v : α}
    (hK : K = {T₁, T₂, T₃})
    (hu : u ∈ sharedPart T₁ T₂ T₃)
    (hv : v ∈ sharedPart T₁ T₃ T₂) :
    ({u, v} : Row α) ∈ blocker K := by
  have huT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hu).1).1
  have huT₂ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hu).1).2
  have huT₃ := (Finset.mem_sdiff.mp hu).2
  have hvT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
  have hvT₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).2
  have hvT₂ := (Finset.mem_sdiff.mp hv).2
  apply pair_mem_blocker_threeRows
  · intro T hT
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl
    · exact ⟨u, by simp, huT₁⟩
    · exact ⟨u, by simp, huT₂⟩
    · exact ⟨v, by simp, hvT₃⟩
  · exact ⟨T₂, by simp [hK], huT₂, hvT₂⟩
  · exact ⟨T₃, by simp [hK], hvT₃, huT₃⟩

theorem threeRow_triple_blockers {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hT₁T₂ : T₁ ≠ T₂) (hT₁T₃ : T₁ ≠ T₃) (hT₂T₃ : T₂ ≠ T₃) :
    rowsCardExactly (blocker K) 3 =
      tripleChoiceRows
        (privatePart T₁ T₂ T₃)
        (privatePart T₂ T₁ T₃)
        (privatePart T₃ T₁ T₂) := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨hTb, hTcard⟩ := mem_rowsCardExactly.mp hT
    have hTmin := mem_blocker.mp hTb
    let privateRow : α → Row α := fun x ↦
      if hx : x ∈ T then Classical.choose (hTmin.exists_privateRow hx) else ∅
    have private_spec {x : α} (hx : x ∈ T) :
        IsPrivateRowFor K T x (privateRow x) := by
      simp only [privateRow, dif_pos hx]
      exact Classical.choose_spec (hTmin.exists_privateRow hx)
    have hMaps : Set.MapsTo privateRow (↑T : Set α) (↑K : Set (Row α)) := by
      intro x hx
      exact (private_spec hx).1
    have hInjective : Set.InjOn privateRow (↑T : Set α) := by
      intro x hx y hy hEq
      have hyPrivate : y ∈ privateRow x := by
        rw [hEq]
        exact (private_spec hy).2.2.1
      exact ((private_spec hx).2.2.2 hy hyPrivate).symm
    have hKcard : K.card = 3 := by simp [hK, hT₁T₂, hT₁T₃, hT₂T₃]
    have hSurj : Set.SurjOn privateRow (↑T : Set α) (↑K : Set (Row α)) :=
      Finset.surjOn_of_injOn_of_card_le privateRow hMaps hInjective (by omega)
    have hT₁K : T₁ ∈ K := by simp [hK]
    have hT₂K : T₂ ∈ K := by simp [hK]
    have hT₃K : T₃ ∈ K := by simp [hK]
    obtain ⟨x₁, hx₁T, hx₁Private⟩ := hSurj hT₁K
    obtain ⟨x₂, hx₂T, hx₂Private⟩ := hSurj hT₂K
    obtain ⟨x₃, hx₃T, hx₃Private⟩ := hSurj hT₃K
    have hx₁x₂ : x₁ ≠ x₂ := by
      intro hEq
      apply hT₁T₂
      rw [← hx₁Private, ← hx₂Private, hEq]
    have hx₁x₃ : x₁ ≠ x₃ := by
      intro hEq
      apply hT₁T₃
      rw [← hx₁Private, ← hx₃Private, hEq]
    have hx₂x₃ : x₂ ≠ x₃ := by
      intro hEq
      apply hT₂T₃
      rw [← hx₂Private, ← hx₃Private, hEq]
    have hx₁Part : x₁ ∈ privatePart T₁ T₂ T₃ := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hx₁Private ▸ (private_spec hx₁T).2.2.1, ?_⟩
      intro hxUnion
      rcases Finset.mem_union.mp hxUnion with hxT₂ | hxT₃
      · have hxEq : x₁ = x₂ :=
          (private_spec hx₂T).2.2.2 hx₁T (hx₂Private ▸ hxT₂)
        exact hx₁x₂ hxEq
      · have hxEq : x₁ = x₃ :=
          (private_spec hx₃T).2.2.2 hx₁T (hx₃Private ▸ hxT₃)
        exact hx₁x₃ hxEq
    have hx₂Part : x₂ ∈ privatePart T₂ T₁ T₃ := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hx₂Private ▸ (private_spec hx₂T).2.2.1, ?_⟩
      intro hxUnion
      rcases Finset.mem_union.mp hxUnion with hxT₁ | hxT₃
      · have hxEq : x₂ = x₁ :=
          (private_spec hx₁T).2.2.2 hx₂T (hx₁Private ▸ hxT₁)
        exact hx₁x₂ hxEq.symm
      · have hxEq : x₂ = x₃ :=
          (private_spec hx₃T).2.2.2 hx₂T (hx₃Private ▸ hxT₃)
        exact hx₂x₃ hxEq
    have hx₃Part : x₃ ∈ privatePart T₃ T₁ T₂ := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hx₃Private ▸ (private_spec hx₃T).2.2.1, ?_⟩
      intro hxUnion
      rcases Finset.mem_union.mp hxUnion with hxT₁ | hxT₂
      · have hxEq : x₃ = x₁ :=
          (private_spec hx₁T).2.2.2 hx₃T (hx₁Private ▸ hxT₁)
        exact hx₁x₃ hxEq.symm
      · have hxEq : x₃ = x₂ :=
          (private_spec hx₂T).2.2.2 hx₃T (hx₂Private ▸ hxT₂)
        exact hx₂x₃ hxEq.symm
    have hTripleSubset : ({x₁, x₂, x₃} : Row α) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hx₁T
      · exact hx₂T
      · exact hx₃T
    have hTripleCard : ({x₁, x₂, x₃} : Row α).card = 3 := by
      simp [hx₁x₂, hx₁x₃, hx₂x₃]
    have hTripleEq : ({x₁, x₂, x₃} : Row α) = T :=
      Finset.eq_of_subset_of_card_le hTripleSubset (by omega)
    exact mem_tripleChoiceRows.mpr
      ⟨x₁, hx₁Part, x₂, hx₂Part, x₃, hx₃Part, hTripleEq⟩
  · intro hT
    obtain ⟨x₁, hx₁Part, x₂, hx₂Part, x₃, hx₃Part, rfl⟩ :=
      mem_tripleChoiceRows.mp hT
    have hx₁T₁ := (Finset.mem_sdiff.mp hx₁Part).1
    have hx₁not := (Finset.mem_sdiff.mp hx₁Part).2
    have hx₂T₂ := (Finset.mem_sdiff.mp hx₂Part).1
    have hx₂not := (Finset.mem_sdiff.mp hx₂Part).2
    have hx₃T₃ := (Finset.mem_sdiff.mp hx₃Part).1
    have hx₃not := (Finset.mem_sdiff.mp hx₃Part).2
    have hx₁x₂ : x₁ ≠ x₂ := by
      intro hEq
      exact hx₁not (Finset.mem_union_left _ (hEq ▸ hx₂T₂))
    have hx₁x₃ : x₁ ≠ x₃ := by
      intro hEq
      exact hx₁not (Finset.mem_union_right _ (hEq ▸ hx₃T₃))
    have hx₂x₃ : x₂ ≠ x₃ := by
      intro hEq
      exact hx₂not (Finset.mem_union_right _ (hEq ▸ hx₃T₃))
    apply mem_rowsCardExactly.mpr
    refine ⟨mem_blocker.mpr ?_, by simp [hx₁x₂, hx₁x₃, hx₂x₃]⟩
    have hTransversal : IsTransversal K {x₁, x₂, x₃} := by
      intro E hE
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl | rfl
      · exact ⟨x₁, by simp, hx₁T₁⟩
      · exact ⟨x₂, by simp, hx₂T₂⟩
      · exact ⟨x₃, by simp, hx₃T₃⟩
    apply hTransversal.minimal_of_privateRows
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨T₁, by simp [hK], by simp, hx₁T₁, by
        intro y hyTriple hyT₁
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyTriple
        rcases hyTriple with rfl | rfl | rfl
        · rfl
        · exact (hx₂not (Finset.mem_union_left _ hyT₁)).elim
        · exact (hx₃not (Finset.mem_union_left _ hyT₁)).elim⟩
    · exact ⟨T₂, by simp [hK], by simp, hx₂T₂, by
        intro y hyTriple hyT₂
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyTriple
        rcases hyTriple with rfl | rfl | rfl
        · exact (hx₁not (Finset.mem_union_left _ hyT₂)).elim
        · rfl
        · exact (hx₃not (Finset.mem_union_right _ hyT₂)).elim⟩
    · exact ⟨T₃, by simp [hK], by simp, hx₃T₃, by
        intro y hyTriple hyT₃
        simp only [Finset.mem_insert, Finset.mem_singleton] at hyTriple
        rcases hyTriple with rfl | rfl | rfl
        · exact (hx₁not (Finset.mem_union_right _ hyT₃)).elim
        · exact (hx₂not (Finset.mem_union_right _ hyT₃)).elim
        · rfl⟩

theorem threeRow_triple_blockers_card {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hT₁T₂ : T₁ ≠ T₂) (hT₁T₃ : T₁ ≠ T₃) (hT₂T₃ : T₂ ≠ T₃) :
    (rowsCardExactly (blocker K) 3).card =
      (privatePart T₁ T₂ T₃).card *
      (privatePart T₂ T₁ T₃).card *
      (privatePart T₃ T₁ T₂).card := by
  rw [threeRow_triple_blockers hK hT₁T₂ hT₁T₃ hT₂T₃]
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := privatePart_pairwise_disjoint T₁ T₂ T₃
  exact tripleChoiceRows_card h₁₂ h₁₃ h₂₃

theorem threeRow_three_pair_blockers_of_private_cards_one_one_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hKRows : RowsCardAtLeast K 2)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hPrivate₁ : (privatePart T₁ T₂ T₃).card = 1)
    (hPrivate₂ : (privatePart T₂ T₁ T₃).card = 1)
    (hPrivate₃ : (privatePart T₃ T₁ T₂).card = 3) :
    3 ≤ (pairRows (blocker K)).card := by
  classical
  let A := privatePart T₁ T₂ T₃
  let B := privatePart T₂ T₁ T₃
  let C := privatePart T₃ T₁ T₂
  let U := sharedPart T₁ T₂ T₃
  let V := sharedPart T₁ T₃ T₂
  let W := sharedPart T₂ T₃ T₁
  have hNoCommon :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hK hBRows
  have row₁_classify {x : α} (hx : x ∈ T₁) : x ∈ A ∨ x ∈ U ∨ x ∈ V := by
    by_cases hx₂ : x ∈ T₂
    · by_cases hx₃ : x ∈ T₃
      · exact (hNoCommon x ⟨hx, hx₂, hx₃⟩).elim
      · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hx, hx₂⟩, hx₃⟩))
    · by_cases hx₃ : x ∈ T₃
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hx, hx₃⟩, hx₂⟩))
      · exact Or.inl (Finset.mem_sdiff.mpr
          ⟨hx, by simp only [Finset.mem_union, not_or]; exact ⟨hx₂, hx₃⟩⟩)
  have row₂_classify {x : α} (hx : x ∈ T₂) : x ∈ B ∨ x ∈ U ∨ x ∈ W := by
    by_cases hx₁ : x ∈ T₁
    · by_cases hx₃ : x ∈ T₃
      · exact (hNoCommon x ⟨hx₁, hx, hx₃⟩).elim
      · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hx₁, hx⟩, hx₃⟩))
    · by_cases hx₃ : x ∈ T₃
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hx, hx₃⟩, hx₁⟩))
      · exact Or.inl (Finset.mem_sdiff.mpr
          ⟨hx, by simp only [Finset.mem_union, not_or]; exact ⟨hx₁, hx₃⟩⟩)
  by_cases hUNonempty : U.Nonempty
  · have hCrossSubset : crossPairRows U C ⊆ pairRows (blocker K) := by
      intro E hE
      obtain ⟨u, huU, c, hcC, rfl⟩ := mem_crossPairRows.mp hE
      have huc : u ≠ c := by
        intro huc
        have huT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp huU).1).1
        exact (Finset.mem_sdiff.mp hcC).2
          (Finset.mem_union_left _ (huc ▸ huT₁))
      exact Finset.mem_filter.mpr
        ⟨shared_private_pair_mem_blocker hK huU hcC, by simp [huc]⟩
    have hUCDisjoint : Disjoint U C := by
      apply Finset.disjoint_left.mpr
      intro x hxU hxC
      have hxT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxU).1).1
      exact (Finset.mem_sdiff.mp hxC).2 (Finset.mem_union_left _ hxT₁)
    have hUcard : 1 ≤ U.card := Finset.one_le_card.mpr hUNonempty
    have hCcard : C.card = 3 := by simpa [C] using hPrivate₃
    calc
      3 = 1 * 3 := rfl
      _ ≤ U.card * C.card := by
        rw [hCcard]
        exact Nat.mul_le_mul_right 3 hUcard
      _ ≤ (crossPairRows U C).card :=
        card_mul_le_crossPairRows_card_of_disjoint hUCDisjoint
      _ ≤ (pairRows (blocker K)).card := Finset.card_le_card hCrossSubset
  · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUNonempty
    have hVNonempty : V.Nonempty := by
      by_contra hV
      have hVempty : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
      have hT₁Subset : T₁ ⊆ A := by
        intro x hx
        rcases row₁_classify hx with hxA | hxU | hxV
        · exact hxA
        · simpa [hUempty] using hxU
        · simpa [hVempty] using hxV
      have hT₁card : T₁.card ≤ 1 := by
        calc
          T₁.card ≤ A.card := Finset.card_le_card hT₁Subset
          _ = 1 := by simpa [A] using hPrivate₁
      have hT₁large := hKRows T₁ (by simp [hK])
      omega
    have hWNonempty : W.Nonempty := by
      by_contra hW
      have hWempty : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
      have hT₂Subset : T₂ ⊆ B := by
        intro x hx
        rcases row₂_classify hx with hxB | hxU | hxW
        · exact hxB
        · simpa [hUempty] using hxU
        · simpa [hWempty] using hxW
      have hT₂card : T₂.card ≤ 1 := by
        calc
          T₂.card ≤ B.card := Finset.card_le_card hT₂Subset
          _ = 1 := by simpa [B] using hPrivate₂
      have hT₂large := hKRows T₂ (by simp [hK])
      omega
    obtain ⟨v, hvV⟩ := hVNonempty
    obtain ⟨w, hwW⟩ := hWNonempty
    have hAcard : A.card = 1 := by simpa [A] using hPrivate₁
    have hBcard : B.card = 1 := by simpa [B] using hPrivate₂
    have hApositive : 0 < A.card := by omega
    have hBpositive : 0 < B.card := by omega
    obtain ⟨a, haA⟩ := Finset.card_pos.mp hApositive
    obtain ⟨b, hbB⟩ := Finset.card_pos.mp hBpositive
    have hvw : v ≠ w := by
      intro hvw
      have hvT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvV).1).1
      exact (Finset.mem_sdiff.mp hwW).2 (hvw ▸ hvT₁)
    have hvb : v ≠ b := by
      intro hvb
      have hbT₂ := (Finset.mem_sdiff.mp hbB).1
      exact (Finset.mem_sdiff.mp hvV).2 (hvb ▸ hbT₂)
    have hwa : w ≠ a := by
      intro hwa
      have haT₁ := (Finset.mem_sdiff.mp haA).1
      exact (Finset.mem_sdiff.mp hwW).2 (hwa ▸ haT₁)
    have hwb : w ≠ b := by
      intro hwb
      have hwT₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hwW).1).2
      have hbNotT₃ : b ∉ T₃ := fun hbT₃ ↦
        (Finset.mem_sdiff.mp hbB).2 (Finset.mem_union_right _ hbT₃)
      exact hbNotT₃ (hwb ▸ hwT₃)
    have hva : v ≠ a := by
      intro hva
      have hvT₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvV).1).2
      have haNotT₃ : a ∉ T₃ := fun haT₃ ↦
        (Finset.mem_sdiff.mp haA).2 (Finset.mem_union_right _ haT₃)
      exact haNotT₃ (hva ▸ hvT₃)
    have hvwPair : ({v, w} : Row α) ∈ pairRows (blocker K) := by
      apply Finset.mem_filter.mpr
      have hvV' : v ∈ sharedPart T₃ T₁ T₂ := by
        obtain ⟨hvInter, hvNot⟩ := Finset.mem_sdiff.mp hvV
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr (Finset.mem_inter.mp hvInter).symm, hvNot⟩
      have hwW' : w ∈ sharedPart T₃ T₂ T₁ := by
        obtain ⟨hwInter, hwNot⟩ := Finset.mem_sdiff.mp hwW
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr (Finset.mem_inter.mp hwInter).symm, hwNot⟩
      refine ⟨shared_shared_pair_mem_blocker
        (K := K) (T₁ := T₃) (T₂ := T₁) (T₃ := T₂)
        (by rw [hK]; ext E; simp [or_comm, or_left_comm]) hvV' hwW', by simp [hvw]⟩
    have hvbPair : ({v, b} : Row α) ∈ pairRows (blocker K) := by
      apply Finset.mem_filter.mpr
      refine ⟨shared_private_pair_mem_blocker
        (K := K) (T₁ := T₁) (T₂ := T₃) (T₃ := T₂)
        (by rw [hK]; ext E; simp [or_comm]) hvV hbB, by simp [hvb]⟩
    have hwaPair : ({w, a} : Row α) ∈ pairRows (blocker K) := by
      apply Finset.mem_filter.mpr
      refine ⟨shared_private_pair_mem_blocker
        (K := K) (T₁ := T₂) (T₂ := T₃) (T₃ := T₁)
        (by rw [hK]; ext E; simp [or_comm, or_left_comm]) hwW haA, by simp [hwa]⟩
    have hFirstSecond : ({v, w} : Row α) ≠ {v, b} := by
      intro hEq
      have hwMem : w ∈ ({v, b} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwMem
      rcases hwMem with hwv | hwb'
      · exact hvw hwv.symm
      · exact hwb hwb'
    have hFirstThird : ({v, w} : Row α) ≠ {w, a} := by
      intro hEq
      have hvMem : v ∈ ({w, a} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvMem
      rcases hvMem with hvw' | hva'
      · exact hvw hvw'
      · exact hva hva'
    have hSecondThird : ({v, b} : Row α) ≠ {w, a} := by
      intro hEq
      have hvMem : v ∈ ({w, a} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvMem
      rcases hvMem with hvw' | hva'
      · exact hvw hvw'
      · exact hva hva'
    have hThreeSubset :
        ({{v, w}, {v, b}, {w, a}} : Hypergraph α) ⊆ pairRows (blocker K) := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl | rfl
      · exact hvwPair
      · exact hvbPair
      · exact hwaPair
    have hThreeCard : ({{v, w}, {v, b}, {w, a}} : Hypergraph α).card = 3 := by
      simp [hFirstSecond, hFirstThird, hSecondThird]
    simpa [hThreeCard] using Finset.card_le_card hThreeSubset

theorem threeRow_three_pair_blockers_of_private_card_product_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hKRows : RowsCardAtLeast K 2)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hPrivateProduct :
      (privatePart T₁ T₂ T₃).card *
        (privatePart T₂ T₁ T₃).card *
        (privatePart T₃ T₁ T₂).card = 3) :
    3 ≤ (pairRows (blocker K)).card := by
  let a := (privatePart T₁ T₂ T₃).card
  let b := (privatePart T₂ T₁ T₃).card
  let c := (privatePart T₃ T₁ T₂).card
  have haDvd : a ∣ 3 := by
    refine ⟨b * c, ?_⟩
    simpa [a, b, c, Nat.mul_assoc] using hPrivateProduct.symm
  have hbDvd : b ∣ 3 := by
    refine ⟨a * c, ?_⟩
    simpa [a, b, c, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hPrivateProduct.symm
  have hcDvd : c ∣ 3 := by
    refine ⟨a * b, ?_⟩
    simpa [a, b, c, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hPrivateProduct.symm
  have haPos : 0 < a := by
    by_contra h
    have haZero : a = 0 := Nat.eq_zero_of_not_pos h
    simp [haZero] at haDvd
  have hbPos : 0 < b := by
    by_contra h
    have hbZero : b = 0 := Nat.eq_zero_of_not_pos h
    simp [hbZero] at hbDvd
  have hcPos : 0 < c := by
    by_contra h
    have hcZero : c = 0 := Nat.eq_zero_of_not_pos h
    simp [hcZero] at hcDvd
  have haLe : a ≤ 3 := Nat.le_of_dvd (by omega) haDvd
  have hbLe : b ≤ 3 := Nat.le_of_dvd (by omega) hbDvd
  have hcLe : c ≤ 3 := Nat.le_of_dvd (by omega) hcDvd
  have haCases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  have hbCases : b = 1 ∨ b = 2 ∨ b = 3 := by omega
  have hcCases : c = 1 ∨ c = 2 ∨ c = 3 := by omega
  have hCases :
      (a = 1 ∧ b = 1 ∧ c = 3) ∨
        (a = 1 ∧ b = 3 ∧ c = 1) ∨
        (a = 3 ∧ b = 1 ∧ c = 1) := by
    rcases haCases with ha | ha | ha <;>
      rcases hbCases with hb | hb | hb <;>
      rcases hcCases with hc | hc | hc <;>
      simp_all [a, b, c]
  rcases hCases with hCards | hCards | hCards
  · exact threeRow_three_pair_blockers_of_private_cards_one_one_three
      hK hKRows hBRows
      (by simpa [a] using hCards.1)
      (by simpa [b] using hCards.2.1)
      (by simpa [c] using hCards.2.2)
  · exact threeRow_three_pair_blockers_of_private_cards_one_one_three
      (T₁ := T₁) (T₂ := T₃) (T₃ := T₂)
      (by rw [hK]; ext E; simp [or_comm]) hKRows hBRows
      (by simpa [a, privatePart, Finset.union_comm] using hCards.1)
      (by simpa [c, privatePart, Finset.union_comm] using hCards.2.2)
      (by simpa [b] using hCards.2.1)
  · exact threeRow_three_pair_blockers_of_private_cards_one_one_three
      (T₁ := T₂) (T₂ := T₃) (T₃ := T₁)
      (by rw [hK]; ext E; simp [or_comm, or_left_comm]) hKRows hBRows
      (by simpa [b, privatePart, Finset.union_comm] using hCards.2.1)
      (by simpa [c, privatePart, Finset.union_comm] using hCards.2.2)
      (by simpa [a] using hCards.1)

theorem threeRow_pairRows_card_eq_two_of_blocker_card_eq_four {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hT₁T₂ : T₁ ≠ T₂) (hT₁T₃ : T₁ ≠ T₃) (hT₂T₃ : T₂ ≠ T₃)
    (hKRows : RowsCardAtLeast K 2)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBcard : (blocker K).card = 4)
    (hPairPositive : 1 ≤ (pairRows (blocker K)).card)
    (hPairUpper : (pairRows (blocker K)).card ≤ 2) :
    (pairRows (blocker K)).card = 2 := by
  classical
  by_contra hPairNotTwo
  have hPairCard : (pairRows (blocker K)).card = 1 := by omega
  have hKcard : K.card = 3 := by simp [hK, hT₁T₂, hT₁T₃, hT₂T₃]
  have hBlockerUpper {E : Row α} (hE : E ∈ blocker K) : E.card ≤ 3 := by
    have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hE)
    omega
  have hPartition :
      pairRows (blocker K) ∪ rowsCardExactly (blocker K) 3 = blocker K := by
    ext E
    constructor
    · intro hE
      rcases Finset.mem_union.mp hE with hPair | hTriple
      · exact (Finset.mem_filter.mp hPair).1
      · exact (mem_rowsCardExactly.mp hTriple).1
    · intro hE
      have hLower := hBRows E hE
      have hUpper := hBlockerUpper hE
      have hCases : E.card = 2 ∨ E.card = 3 := by omega
      rcases hCases with hCard | hCard
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hE, hCard⟩)
      · exact Finset.mem_union_right _ (mem_rowsCardExactly.mpr ⟨hE, hCard⟩)
  have hDisjoint :
      Disjoint (pairRows (blocker K)) (rowsCardExactly (blocker K) 3) := by
    apply Finset.disjoint_left.mpr
    intro E hPair hTriple
    have hTwo := (Finset.mem_filter.mp hPair).2
    have hThree := (mem_rowsCardExactly.mp hTriple).2
    omega
  have hCardAdd :
      (pairRows (blocker K)).card + (rowsCardExactly (blocker K) 3).card =
        (blocker K).card := by
    calc
      (pairRows (blocker K)).card + (rowsCardExactly (blocker K) 3).card =
          (pairRows (blocker K) ∪ rowsCardExactly (blocker K) 3).card :=
        (Finset.card_union_of_disjoint hDisjoint).symm
      _ = (blocker K).card := congrArg Finset.card hPartition
  have hTripleCard : (rowsCardExactly (blocker K) 3).card = 3 := by omega
  have hPrivateProduct :=
    threeRow_triple_blockers_card hK hT₁T₂ hT₁T₃ hT₂T₃
  rw [hTripleCard] at hPrivateProduct
  have hThreePairs := threeRow_three_pair_blockers_of_private_card_product_three
    hK hKRows hBRows hPrivateProduct.symm
  omega

theorem threeRow_two_pair_normal_form_of_private_cards_one_one_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hT₁T₂ : T₁ ≠ T₂) (hT₁T₃ : T₁ ≠ T₃) (hT₂T₃ : T₂ ≠ T₃)
    (hKRows : RowsCardAtLeast K 2)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBcard : (blocker K).card = 4)
    (hPairCard : (pairRows (blocker K)).card = 2)
    (hPrivate₁ : (privatePart T₁ T₂ T₃).card = 1)
    (hPrivate₂ : (privatePart T₂ T₁ T₃).card = 1)
    (hPrivate₃ : (privatePart T₃ T₁ T₂).card = 2) :
    ∃ u a b c₁ c₂,
      u ≠ a ∧ u ≠ b ∧ u ≠ c₁ ∧ u ≠ c₂ ∧
      a ≠ b ∧ a ≠ c₁ ∧ a ≠ c₂ ∧
      b ≠ c₁ ∧ b ≠ c₂ ∧ c₁ ≠ c₂ ∧
      blocker K = {{u, c₁}, {u, c₂}, {a, b, c₁}, {a, b, c₂}} := by
  classical
  let A := privatePart T₁ T₂ T₃
  let B := privatePart T₂ T₁ T₃
  let C := privatePart T₃ T₁ T₂
  let U := sharedPart T₁ T₂ T₃
  let V := sharedPart T₁ T₃ T₂
  let W := sharedPart T₂ T₃ T₁
  have hNoCommon :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hK hBRows
  have row₁_classify {x : α} (hx : x ∈ T₁) : x ∈ A ∨ x ∈ U ∨ x ∈ V := by
    by_cases hx₂ : x ∈ T₂
    · by_cases hx₃ : x ∈ T₃
      · exact (hNoCommon x ⟨hx, hx₂, hx₃⟩).elim
      · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hx, hx₂⟩, hx₃⟩))
    · by_cases hx₃ : x ∈ T₃
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hx, hx₃⟩, hx₂⟩))
      · exact Or.inl (Finset.mem_sdiff.mpr
          ⟨hx, by simp only [Finset.mem_union, not_or]; exact ⟨hx₂, hx₃⟩⟩)
  have row₂_classify {x : α} (hx : x ∈ T₂) : x ∈ B ∨ x ∈ U ∨ x ∈ W := by
    by_cases hx₁ : x ∈ T₁
    · by_cases hx₃ : x ∈ T₃
      · exact (hNoCommon x ⟨hx₁, hx, hx₃⟩).elim
      · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hx₁, hx⟩, hx₃⟩))
    · by_cases hx₃ : x ∈ T₃
      · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr ⟨hx, hx₃⟩, hx₁⟩))
      · exact Or.inl (Finset.mem_sdiff.mpr
          ⟨hx, by simp only [Finset.mem_union, not_or]; exact ⟨hx₁, hx₃⟩⟩)
  have hUNonempty : U.Nonempty := by
    by_contra hU
    have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    have hVNonempty : V.Nonempty := by
      by_contra hV
      have hVempty : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
      have hT₁Subset : T₁ ⊆ A := by
        intro x hx
        rcases row₁_classify hx with hxA | hxU | hxV
        · exact hxA
        · simpa [hUempty] using hxU
        · simpa [hVempty] using hxV
      have hT₁card : T₁.card ≤ 1 := by
        calc
          T₁.card ≤ A.card := Finset.card_le_card hT₁Subset
          _ = 1 := by simpa [A] using hPrivate₁
      have hT₁K : T₁ ∈ K := by simp [hK]
      have := hKRows T₁ hT₁K
      omega
    have hWNonempty : W.Nonempty := by
      by_contra hW
      have hWempty : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
      have hT₂Subset : T₂ ⊆ B := by
        intro x hx
        rcases row₂_classify hx with hxB | hxU | hxW
        · exact hxB
        · simpa [hUempty] using hxU
        · simpa [hWempty] using hxW
      have hT₂card : T₂.card ≤ 1 := by
        calc
          T₂.card ≤ B.card := Finset.card_le_card hT₂Subset
          _ = 1 := by simpa [B] using hPrivate₂
      have hT₂K : T₂ ∈ K := by simp [hK]
      have := hKRows T₂ hT₂K
      omega
    obtain ⟨v, hvV⟩ := hVNonempty
    obtain ⟨w, hwW⟩ := hWNonempty
    have hApositive : 0 < A.card := by simpa [A, hPrivate₁]
    have hBpositive : 0 < B.card := by simpa [B, hPrivate₂]
    obtain ⟨a, haA⟩ := Finset.card_pos.mp hApositive
    obtain ⟨b, hbB⟩ := Finset.card_pos.mp hBpositive
    have hvw : v ≠ w := by
      intro hvw
      have hvT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvV).1).1
      have hwNotT₁ := (Finset.mem_sdiff.mp hwW).2
      exact hwNotT₁ (hvw ▸ hvT₁)
    have hvb : v ≠ b := by
      intro hvb
      have hvNotT₂ := (Finset.mem_sdiff.mp hvV).2
      have hbT₂ := (Finset.mem_sdiff.mp hbB).1
      exact hvNotT₂ (hvb ▸ hbT₂)
    have hwa : w ≠ a := by
      intro hwa
      have hwNotT₁ := (Finset.mem_sdiff.mp hwW).2
      have haT₁ := (Finset.mem_sdiff.mp haA).1
      exact hwNotT₁ (hwa ▸ haT₁)
    have hwb : w ≠ b := by
      intro hwb
      have hwT₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hwW).1).2
      have hbNotT₃ : b ∉ T₃ := fun hbT₃ ↦
        (Finset.mem_sdiff.mp hbB).2 (Finset.mem_union_right _ hbT₃)
      exact hbNotT₃ (hwb ▸ hwT₃)
    have hva : v ≠ a := by
      intro hva
      have hvT₃ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvV).1).2
      have haNotT₃ : a ∉ T₃ := fun haT₃ ↦
        (Finset.mem_sdiff.mp haA).2 (Finset.mem_union_right _ haT₃)
      exact haNotT₃ (hva ▸ hvT₃)
    have hab : a ≠ b := by
      intro hab
      have haT₁ := (Finset.mem_sdiff.mp haA).1
      have hbNotT₁ : b ∉ T₁ := fun hbT₁ ↦
        (Finset.mem_sdiff.mp hbB).2 (Finset.mem_union_left _ hbT₁)
      exact hbNotT₁ (hab ▸ haT₁)
    have hvwb : ({v, w} : Row α) ∈ pairRows (blocker K) := by
      apply Finset.mem_filter.mpr
      have hvV' : v ∈ sharedPart T₃ T₁ T₂ := by
        obtain ⟨hvInter, hvNot⟩ := Finset.mem_sdiff.mp hvV
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr (Finset.mem_inter.mp hvInter).symm, hvNot⟩
      have hwW' : w ∈ sharedPart T₃ T₂ T₁ := by
        obtain ⟨hwInter, hwNot⟩ := Finset.mem_sdiff.mp hwW
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_inter.mpr (Finset.mem_inter.mp hwInter).symm, hwNot⟩
      refine ⟨shared_shared_pair_mem_blocker
        (K := K) (T₁ := T₃) (T₂ := T₁) (T₃ := T₂)
        (by rw [hK]; ext E; simp [or_comm, or_left_comm]) hvV' hwW', by simp [hvw]⟩
    have hvbb : ({v, b} : Row α) ∈ pairRows (blocker K) := by
      apply Finset.mem_filter.mpr
      change v ∈ sharedPart T₁ T₃ T₂ at hvV
      change b ∈ privatePart T₂ T₁ T₃ at hbB
      refine ⟨shared_private_pair_mem_blocker
        (K := K) (T₁ := T₁) (T₂ := T₃) (T₃ := T₂)
        (by rw [hK]; ext E; simp [or_comm]) hvV hbB, by simp [hvb]⟩
    have hwab : ({w, a} : Row α) ∈ pairRows (blocker K) := by
      apply Finset.mem_filter.mpr
      change w ∈ sharedPart T₂ T₃ T₁ at hwW
      change a ∈ privatePart T₁ T₂ T₃ at haA
      refine ⟨shared_private_pair_mem_blocker
        (K := K) (T₁ := T₂) (T₂ := T₃) (T₃ := T₁)
        (by rw [hK]; ext E; simp [or_comm, or_left_comm]) hwW haA, by simp [hwa]⟩
    have hFirstSecond : ({v, w} : Row α) ≠ {v, b} := by
      intro hEq
      have hwMem : w ∈ ({v, b} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwMem
      rcases hwMem with hwv | hwb'
      · exact hvw hwv.symm
      · exact hwb hwb'
    have hFirstThird : ({v, w} : Row α) ≠ {w, a} := by
      intro hEq
      have hvMem : v ∈ ({w, a} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvMem
      rcases hvMem with hvw' | hva'
      · exact hvw hvw'
      · exact hva hva'
    have hSecondThird : ({v, b} : Row α) ≠ {w, a} := by
      intro hEq
      have hvMem : v ∈ ({w, a} : Row α) := hEq ▸ (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvMem
      rcases hvMem with hvw' | hva'
      · exact hvw hvw'
      · exact hva hva'
    have hThreeSubset :
        ({{v, w}, {v, b}, {w, a}} : Hypergraph α) ⊆ pairRows (blocker K) := by
      intro E hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl | rfl
      · exact hvwb
      · exact hvbb
      · exact hwab
    have hThreeCard := Finset.card_le_card hThreeSubset
    have hFamilyCard : ({{v, w}, {v, b}, {w, a}} : Hypergraph α).card = 3 := by
      simp [hFirstSecond, hFirstThird, hSecondThird]
    rw [hFamilyCard, hPairCard] at hThreeCard
    omega
  obtain ⟨u, huU⟩ := hUNonempty
  have hCrossSubset : crossPairRows U C ⊆ pairRows (blocker K) := by
    intro E hE
    obtain ⟨x, hxU, c, hcC, rfl⟩ := mem_crossPairRows.mp hE
    have hxc : x ≠ c := by
      intro hxc
      have hxT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxU).1).1
      have hcNotT₁ : c ∉ T₁ := fun hcT₁ ↦
        (Finset.mem_sdiff.mp hcC).2 (Finset.mem_union_left _ hcT₁)
      exact hcNotT₁ (hxc ▸ hxT₁)
    exact Finset.mem_filter.mpr
      ⟨shared_private_pair_mem_blocker hK hxU hcC, by simp [hxc]⟩
  have hUCDisjoint : Disjoint U C := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxC
    have hxT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxU).1).1
    exact (Finset.mem_sdiff.mp hxC).2 (Finset.mem_union_left _ hxT₁)
  have hCrossLower : U.card * C.card ≤ (crossPairRows U C).card :=
    card_mul_le_crossPairRows_card_of_disjoint hUCDisjoint
  have hCrossUpper := Finset.card_le_card hCrossSubset
  have hUcard : U.card = 1 := by
    have hUpositive : 0 < U.card := Finset.card_pos.mpr ⟨u, huU⟩
    have hCcard : C.card = 2 := by simpa [C] using hPrivate₃
    rw [hCcard] at hCrossLower
    rw [hPairCard] at hCrossUpper
    omega
  have hCrossCard : (crossPairRows U C).card = 2 := by
    have hCcard : C.card = 2 := by simpa [C] using hPrivate₃
    rw [hUcard, hCcard] at hCrossLower
    rw [hPairCard] at hCrossUpper
    omega
  have hCrossEq : crossPairRows U C = pairRows (blocker K) :=
    Finset.eq_of_subset_of_card_le hCrossSubset (by omega)
  have hVempty : V = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hvV
    have hBpositive : 0 < B.card := by simpa [B, hPrivate₂]
    obtain ⟨b, hbB⟩ := Finset.card_pos.mp hBpositive
    have hvb : v ≠ b := by
      intro hvb
      have hvNotT₂ := (Finset.mem_sdiff.mp hvV).2
      have hbT₂ := (Finset.mem_sdiff.mp hbB).1
      exact hvNotT₂ (hvb ▸ hbT₂)
    have hPairBlocker : ({v, b} : Row α) ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr
        ⟨shared_private_pair_mem_blocker
          (K := K) (T₁ := T₁) (T₂ := T₃) (T₃ := T₂)
          (by rw [hK]; ext E; simp [or_comm]) hvV hbB, by simp [hvb]⟩
    have hCross : ({v, b} : Row α) ∈ crossPairRows U C := by
      rw [hCrossEq]
      exact hPairBlocker
    obtain ⟨x, hxU, c, hcC, hEq⟩ := mem_crossPairRows.mp hCross
    have hvMem : v ∈ ({x, c} : Row α) := hEq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvMem
    rcases hvMem with hvx | hvc
    · have hvNotT₂ := (Finset.mem_sdiff.mp hvV).2
      have hxT₂ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxU).1).2
      exact hvNotT₂ (hvx ▸ hxT₂)
    · have hvT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvV).1).1
      have hcNotT₁ : c ∉ T₁ := fun hcT₁ ↦
        (Finset.mem_sdiff.mp hcC).2 (Finset.mem_union_left _ hcT₁)
      exact hcNotT₁ (hvc ▸ hvT₁)
  have hWempty : W = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hwW
    have hApositive : 0 < A.card := by simpa [A, hPrivate₁]
    obtain ⟨a, haA⟩ := Finset.card_pos.mp hApositive
    have hwa : w ≠ a := by
      intro hwa
      have hwNotT₁ := (Finset.mem_sdiff.mp hwW).2
      have haT₁ := (Finset.mem_sdiff.mp haA).1
      exact hwNotT₁ (hwa ▸ haT₁)
    have hPairBlocker : ({w, a} : Row α) ∈ pairRows (blocker K) :=
      Finset.mem_filter.mpr
        ⟨shared_private_pair_mem_blocker
          (K := K) (T₁ := T₂) (T₂ := T₃) (T₃ := T₁)
          (by rw [hK]; ext E; simp [or_comm, or_left_comm]) hwW haA, by simp [hwa]⟩
    have hCross : ({w, a} : Row α) ∈ crossPairRows U C := by
      rw [hCrossEq]
      exact hPairBlocker
    obtain ⟨x, hxU, c, hcC, hEq⟩ := mem_crossPairRows.mp hCross
    have hwMem : w ∈ ({x, c} : Row α) := hEq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwMem
    rcases hwMem with hwx | hwc
    · have hwNotT₁ := (Finset.mem_sdiff.mp hwW).2
      have hxT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxU).1).1
      exact hwNotT₁ (hwx ▸ hxT₁)
    · have hwT₂ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hwW).1).1
      have hcNotT₂ : c ∉ T₂ := fun hcT₂ ↦
        (Finset.mem_sdiff.mp hcC).2 (Finset.mem_union_right _ hcT₂)
      exact hcNotT₂ (hwc ▸ hwT₂)
  obtain ⟨a, hAeq⟩ := Finset.card_eq_one.mp (by simpa [A] using hPrivate₁)
  obtain ⟨b, hBeq⟩ := Finset.card_eq_one.mp (by simpa [B] using hPrivate₂)
  obtain ⟨u', hUeq⟩ := Finset.card_eq_one.mp hUcard
  obtain ⟨c₁, c₂, hc₁c₂, hCeq⟩ := Finset.card_eq_two.mp (by simpa [C] using hPrivate₃)
  change A = {a} at hAeq
  change B = {b} at hBeq
  change U = {u'} at hUeq
  change C = {c₁, c₂} at hCeq
  have huu' : u = u' := by simpa [hUeq] using huU
  subst u'
  have haA : a ∈ A := by simp [hAeq]
  have hbB : b ∈ B := by simp [hBeq]
  have huU' : u ∈ U := by simp [hUeq]
  have hc₁C : c₁ ∈ C := by simp [hCeq]
  have hc₂C : c₂ ∈ C := by simp [hCeq]
  have huNeA : u ≠ a := by
    intro hEq
    have huT₂ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp huU').1).2
    have haNotT₂ : a ∉ T₂ := fun haT₂ ↦
      (Finset.mem_sdiff.mp haA).2 (Finset.mem_union_left _ haT₂)
    exact haNotT₂ (hEq ▸ huT₂)
  have huNeB : u ≠ b := by
    intro hEq
    have huT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp huU').1).1
    have hbNotT₁ : b ∉ T₁ := fun hbT₁ ↦
      (Finset.mem_sdiff.mp hbB).2 (Finset.mem_union_left _ hbT₁)
    exact hbNotT₁ (hEq ▸ huT₁)
  have huNeC₁ : u ≠ c₁ := by
    intro hEq
    have huT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp huU').1).1
    exact (Finset.mem_sdiff.mp hc₁C).2 (Finset.mem_union_left _ (hEq ▸ huT₁))
  have huNeC₂ : u ≠ c₂ := by
    intro hEq
    have huT₁ := (Finset.mem_inter.mp (Finset.mem_sdiff.mp huU').1).1
    exact (Finset.mem_sdiff.mp hc₂C).2 (Finset.mem_union_left _ (hEq ▸ huT₁))
  have haNeB : a ≠ b := by
    intro hEq
    have haT₁ := (Finset.mem_sdiff.mp haA).1
    exact (Finset.mem_sdiff.mp hbB).2 (Finset.mem_union_left _ (hEq ▸ haT₁))
  have haNeC₁ : a ≠ c₁ := by
    intro hEq
    have haT₁ := (Finset.mem_sdiff.mp haA).1
    exact (Finset.mem_sdiff.mp hc₁C).2 (Finset.mem_union_left _ (hEq ▸ haT₁))
  have haNeC₂ : a ≠ c₂ := by
    intro hEq
    have haT₁ := (Finset.mem_sdiff.mp haA).1
    exact (Finset.mem_sdiff.mp hc₂C).2 (Finset.mem_union_left _ (hEq ▸ haT₁))
  have hbNeC₁ : b ≠ c₁ := by
    intro hEq
    have hbT₂ := (Finset.mem_sdiff.mp hbB).1
    exact (Finset.mem_sdiff.mp hc₁C).2 (Finset.mem_union_right _ (hEq ▸ hbT₂))
  have hbNeC₂ : b ≠ c₂ := by
    intro hEq
    have hbT₂ := (Finset.mem_sdiff.mp hbB).1
    exact (Finset.mem_sdiff.mp hc₂C).2 (Finset.mem_union_right _ (hEq ▸ hbT₂))
  have hPairEq : pairRows (blocker K) = {{u, c₁}, {u, c₂}} := by
    rw [← hCrossEq]
    ext E
    constructor
    · intro hE
      obtain ⟨x, hxU, c, hcC, hxcE⟩ := mem_crossPairRows.mp hE
      have hxu : x = u := by simpa [hUeq] using hxU
      have hcCases : c = c₁ ∨ c = c₂ := by
        rw [hCeq] at hcC
        simpa using hcC
      rcases hcCases with rfl | rfl
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (by simpa [hxu] using hxcE.symm)
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (by simpa [hxu] using hxcE.symm)
    · intro hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl
      · exact mem_crossPairRows.mpr
          ⟨u, by simp [hUeq], c₁, by simp [hCeq], rfl⟩
      · exact mem_crossPairRows.mpr
          ⟨u, by simp [hUeq], c₂, by simp [hCeq], rfl⟩
  have hTripleEq : rowsCardExactly (blocker K) 3 =
      {{a, b, c₁}, {a, b, c₂}} := by
    rw [threeRow_triple_blockers hK hT₁T₂ hT₁T₃ hT₂T₃]
    ext E
    constructor
    · intro hE
      obtain ⟨x, hxA, y, hyB, c, hcC, hxycE⟩ := mem_tripleChoiceRows.mp hE
      change x ∈ A at hxA
      change y ∈ B at hyB
      change c ∈ C at hcC
      have hxa : x = a := by rw [hAeq] at hxA; simpa using hxA
      have hyb : y = b := by rw [hBeq] at hyB; simpa using hyB
      have hcCases : c = c₁ ∨ c = c₂ := by rw [hCeq] at hcC; simpa using hcC
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hcCases with rfl | rfl
      · exact Or.inl (by simpa [hxa, hyb] using hxycE.symm)
      · exact Or.inr (by simpa [hxa, hyb] using hxycE.symm)
    · intro hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with rfl | rfl
      · exact mem_tripleChoiceRows.mpr
          ⟨a, by change a ∈ A; simp [hAeq],
            b, by change b ∈ B; simp [hBeq],
            c₁, by change c₁ ∈ C; simp [hCeq], rfl⟩
      · exact mem_tripleChoiceRows.mpr
          ⟨a, by change a ∈ A; simp [hAeq],
            b, by change b ∈ B; simp [hBeq],
            c₂, by change c₂ ∈ C; simp [hCeq], rfl⟩
  refine ⟨u, a, b, c₁, c₂, huNeA, huNeB, huNeC₁, huNeC₂,
    haNeB, haNeC₁, haNeC₂, hbNeC₁, hbNeC₂, hc₁c₂, ?_⟩
  ext E
  constructor
  · intro hE
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hLower := hBRows E hE
    have hUpper : E.card ≤ 3 := by
      have := minimalTransversal_card_le_rows (mem_blocker.mp hE)
      have hKcard : K.card = 3 := by simp [hK, hT₁T₂, hT₁T₃, hT₂T₃]
      omega
    have hCases : E.card = 2 ∨ E.card = 3 := by omega
    rcases hCases with hEcard | hEcard
    · have hEPair : E ∈ pairRows (blocker K) :=
        Finset.mem_filter.mpr ⟨hE, hEcard⟩
      have hPairCases : E = {u, c₁} ∨ E = {u, c₂} := by
        simpa [hPairEq] using hEPair
      exact hPairCases.elim (fun h ↦ Or.inl h)
        (fun h ↦ Or.inr (Or.inl h))
    · have hETriple : E ∈ rowsCardExactly (blocker K) 3 :=
        mem_rowsCardExactly.mpr ⟨hE, hEcard⟩
      have hTripleCases : E = {a, b, c₁} ∨ E = {a, b, c₂} := by
        simpa [hTripleEq] using hETriple
      exact hTripleCases.elim
        (fun h ↦ Or.inr (Or.inr (Or.inl h)))
        (fun h ↦ Or.inr (Or.inr (Or.inr h)))
  · intro hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact (Finset.mem_filter.mp (by simp [hPairEq] :
        ({u, c₁} : Row α) ∈ pairRows (blocker K))).1
    · exact (Finset.mem_filter.mp (by simp [hPairEq] :
        ({u, c₂} : Row α) ∈ pairRows (blocker K))).1
    · exact (mem_rowsCardExactly.mp (by simp [hTripleEq] :
        ({a, b, c₁} : Row α) ∈ rowsCardExactly (blocker K) 3)).1
    · exact (mem_rowsCardExactly.mp (by simp [hTripleEq] :
        ({a, b, c₂} : Row α) ∈ rowsCardExactly (blocker K) 3)).1

theorem threeRow_two_pair_normal_form_of_private_card_product_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hT₁T₂ : T₁ ≠ T₂) (hT₁T₃ : T₁ ≠ T₃) (hT₂T₃ : T₂ ≠ T₃)
    (hKRows : RowsCardAtLeast K 2)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBcard : (blocker K).card = 4)
    (hPairCard : (pairRows (blocker K)).card = 2)
    (hPrivateProduct :
      (privatePart T₁ T₂ T₃).card *
        (privatePart T₂ T₁ T₃).card *
        (privatePart T₃ T₁ T₂).card = 2) :
    ∃ u a b c₁ c₂,
      u ≠ a ∧ u ≠ b ∧ u ≠ c₁ ∧ u ≠ c₂ ∧
      a ≠ b ∧ a ≠ c₁ ∧ a ≠ c₂ ∧
      b ≠ c₁ ∧ b ≠ c₂ ∧ c₁ ≠ c₂ ∧
      blocker K = {{u, c₁}, {u, c₂}, {a, b, c₁}, {a, b, c₂}} := by
  let a := (privatePart T₁ T₂ T₃).card
  let b := (privatePart T₂ T₁ T₃).card
  let c := (privatePart T₃ T₁ T₂).card
  have haPos : 0 < a := by
    by_contra h
    have haZero : a = 0 := Nat.eq_zero_of_not_pos h
    simp [a, b, c, haZero] at hPrivateProduct
  have hbPos : 0 < b := by
    by_contra h
    have hbZero : b = 0 := Nat.eq_zero_of_not_pos h
    simp [a, b, c, hbZero] at hPrivateProduct
  have hcPos : 0 < c := by
    by_contra h
    have hcZero : c = 0 := Nat.eq_zero_of_not_pos h
    simp [a, b, c, hcZero] at hPrivateProduct
  have haDvd : a ∣ 2 := by
    refine ⟨b * c, ?_⟩
    simpa [a, b, c, Nat.mul_assoc] using hPrivateProduct.symm
  have hbDvd : b ∣ 2 := by
    refine ⟨a * c, ?_⟩
    simpa [a, b, c, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hPrivateProduct.symm
  have hcDvd : c ∣ 2 := by
    refine ⟨a * b, ?_⟩
    simpa [a, b, c, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hPrivateProduct.symm
  have haLe : a ≤ 2 := Nat.le_of_dvd (by omega) haDvd
  have hbLe : b ≤ 2 := Nat.le_of_dvd (by omega) hbDvd
  have hcLe : c ≤ 2 := Nat.le_of_dvd (by omega) hcDvd
  have hCases :
      (a = 1 ∧ b = 1 ∧ c = 2) ∨
        (a = 1 ∧ b = 2 ∧ c = 1) ∨
        (a = 2 ∧ b = 1 ∧ c = 1) := by
    have haCases : a = 1 ∨ a = 2 := by omega
    have hbCases : b = 1 ∨ b = 2 := by omega
    have hcCases : c = 1 ∨ c = 2 := by omega
    rcases haCases with ha | ha <;>
      rcases hbCases with hb | hb <;>
      rcases hcCases with hc | hc <;>
      simp_all [a, b, c]
  rcases hCases with hCards | hCards | hCards
  · exact threeRow_two_pair_normal_form_of_private_cards_one_one_two
      hK hT₁T₂ hT₁T₃ hT₂T₃ hKRows hBRows hBcard hPairCard
      (by simpa [a] using hCards.1)
      (by simpa [b] using hCards.2.1)
      (by simpa [c] using hCards.2.2)
  · exact threeRow_two_pair_normal_form_of_private_cards_one_one_two
      (T₁ := T₁) (T₂ := T₃) (T₃ := T₂)
      (by rw [hK]; ext E; simp [or_comm])
      hT₁T₃ hT₁T₂ hT₂T₃.symm hKRows hBRows hBcard hPairCard
      (by simpa [a, privatePart, Finset.union_comm] using hCards.1)
      (by simpa [c, privatePart, Finset.union_comm] using hCards.2.2)
      (by simpa [b] using hCards.2.1)
  · exact threeRow_two_pair_normal_form_of_private_cards_one_one_two
      (T₁ := T₂) (T₂ := T₃) (T₃ := T₁)
      (by rw [hK]; ext E; simp [or_comm, or_left_comm])
      hT₂T₃ hT₁T₂.symm hT₁T₃.symm hKRows hBRows hBcard hPairCard
      (by simpa [b, privatePart, Finset.union_comm] using hCards.2.1)
      (by simpa [c, privatePart, Finset.union_comm] using hCards.2.2)
      (by simpa [a] using hCards.1)

theorem threeRow_two_pair_normal_form {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hT₁T₂ : T₁ ≠ T₂) (hT₁T₃ : T₁ ≠ T₃) (hT₂T₃ : T₂ ≠ T₃)
    (hKRows : RowsCardAtLeast K 2)
    (hBRows : RowsCardAtLeast (blocker K) 2)
    (hBcard : (blocker K).card = 4)
    (hPairCard : (pairRows (blocker K)).card = 2) :
    ∃ u a b c₁ c₂,
      u ≠ a ∧ u ≠ b ∧ u ≠ c₁ ∧ u ≠ c₂ ∧
      a ≠ b ∧ a ≠ c₁ ∧ a ≠ c₂ ∧
      b ≠ c₁ ∧ b ≠ c₂ ∧ c₁ ≠ c₂ ∧
      blocker K = {{u, c₁}, {u, c₂}, {a, b, c₁}, {a, b, c₂}} := by
  classical
  have hKcard : K.card = 3 := by simp [hK, hT₁T₂, hT₁T₃, hT₂T₃]
  have hBlockerUpper {E : Row α} (hE : E ∈ blocker K) : E.card ≤ 3 := by
    have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hE)
    omega
  have hPartition :
      pairRows (blocker K) ∪ rowsCardExactly (blocker K) 3 = blocker K := by
    ext E
    constructor
    · intro hE
      rcases Finset.mem_union.mp hE with hPair | hTriple
      · exact (Finset.mem_filter.mp hPair).1
      · exact (mem_rowsCardExactly.mp hTriple).1
    · intro hE
      have hLower := hBRows E hE
      have hUpper := hBlockerUpper hE
      have hCases : E.card = 2 ∨ E.card = 3 := by omega
      rcases hCases with hCard | hCard
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hE, hCard⟩)
      · exact Finset.mem_union_right _ (mem_rowsCardExactly.mpr ⟨hE, hCard⟩)
  have hDisjoint :
      Disjoint (pairRows (blocker K)) (rowsCardExactly (blocker K) 3) := by
    apply Finset.disjoint_left.mpr
    intro E hPair hTriple
    have hTwo := (Finset.mem_filter.mp hPair).2
    have hThree := (mem_rowsCardExactly.mp hTriple).2
    omega
  have hCardAdd :
      (pairRows (blocker K)).card + (rowsCardExactly (blocker K) 3).card =
        (blocker K).card := by
    calc
      (pairRows (blocker K)).card + (rowsCardExactly (blocker K) 3).card =
          (pairRows (blocker K) ∪ rowsCardExactly (blocker K) 3).card :=
        (Finset.card_union_of_disjoint hDisjoint).symm
      _ = (blocker K).card := congrArg Finset.card hPartition
  have hTripleCard : (rowsCardExactly (blocker K) 3).card = 2 := by omega
  have hPrivateProduct :=
    threeRow_triple_blockers_card hK hT₁T₂ hT₁T₃ hT₂T₃
  rw [hTripleCard] at hPrivateProduct
  exact threeRow_two_pair_normal_form_of_private_card_product_two
    hK hT₁T₂ hT₁T₃ hT₂T₃ hKRows hBRows hBcard hPairCard
    hPrivateProduct.symm

end AiMathLab.P0054.G413
