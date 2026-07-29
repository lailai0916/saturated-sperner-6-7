import AiMathLab.P0054G413.SmallRows

namespace AiMathLab.P0054.G413

theorem IsTransversal.minimal_of_privateRows {α : Type*}
    {H : Hypergraph α} {T : Row α} (hT : IsTransversal H T)
    (hPrivate : ∀ x ∈ T, ∃ E, IsPrivateRowFor H T x E) :
    IsMinimalTransversal H T := by
  refine isMinimalTransversal_iff.mpr ⟨hT, ?_⟩
  intro S hST hS
  obtain ⟨x, hxT, hxS⟩ := Finset.not_subset.mp hST.not_subset
  obtain ⟨E, hE⟩ := hPrivate x hxT
  obtain ⟨y, hyS, hyE⟩ := hS E hE.1
  have hyT : y ∈ T := hST.le hyS
  have hyx : y = x := hE.2.2.2 hyT hyE
  exact hxS (hyx ▸ hyS)

theorem no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (hBRows : RowsCardAtLeast (blocker K) 2) :
    ∀ x, ¬(x ∈ T₁ ∧ x ∈ T₂ ∧ x ∈ T₃) := by
  intro x hx
  have hSingletonTransversal : IsTransversal K {x} := by
    intro T hTK
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hTK
    rcases hTK with rfl | rfl | rfl
    · exact ⟨x, by simp, hx.1⟩
    · exact ⟨x, by simp, hx.2.1⟩
    · exact ⟨x, by simp, hx.2.2⟩
  have hSingletonMinimal : IsMinimalTransversal K {x} := by
    refine isMinimalTransversal_iff.mpr ⟨hSingletonTransversal, ?_⟩
    intro S hS hTransversal
    have hSEmpty : S = ∅ := Finset.eq_empty_of_ssubset_singleton hS
    subst S
    obtain ⟨y, hyEmpty, -⟩ := hTransversal T₁ (by simp [hK])
    simp at hyEmpty
  have hSingletonBlocker : ({x} : Row α) ∈ blocker K :=
    mem_blocker.mpr hSingletonMinimal
  have hLarge := hBRows {x} hSingletonBlocker
  simp at hLarge

theorem exists_replacement_blocker_threeRows {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ A : Row α} {x₁ x₂ x₃ y : α}
    (hK : K = {T₁, T₂, T₃})
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃)
    (hPrivate₁ : IsPrivateRowFor K A x₁ T₁)
    (hPrivate₂ : IsPrivateRowFor K A x₂ T₂)
    (hPrivate₃ : IsPrivateRowFor K A x₃ T₃)
    (hyT₁ : y ∈ T₁) (_hyA : y ∉ A) :
    ∃ R ∈ blocker K,
      y ∈ R ∧ R ⊆ insert y (A.erase x₁) ∧
      ∀ z ∈ R, z ∉ A → z = y := by
  let S : Row α := insert y (A.erase x₁)
  have hSTransversal : IsTransversal K S := by
    intro T hTK
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hTK
    rcases hTK with rfl | rfl | rfl
    · exact ⟨y, by simp [S], hyT₁⟩
    · exact ⟨x₂, by simp [S, hx₁x₂.symm, hPrivate₂.2.1], hPrivate₂.2.2.1⟩
    · exact ⟨x₃, by simp [S, hx₁x₃.symm, hPrivate₃.2.1], hPrivate₃.2.2.1⟩
  obtain ⟨R, hRS, hRMinimal⟩ := exists_minimalTransversal_subset hSTransversal
  have hyR : y ∈ R := by
    obtain ⟨z, hzR, hzT₁⟩ := hRMinimal.prop T₁ hPrivate₁.1
    have hzS := hRS hzR
    simp only [S, Finset.mem_insert, Finset.mem_erase] at hzS
    rcases hzS with hzy | ⟨hzx₁, hzA⟩
    · exact hzy ▸ hzR
    · have hzx₁' : z = x₁ := hPrivate₁.2.2.2 hzA hzT₁
      exact (hzx₁ hzx₁').elim
  refine ⟨R, mem_blocker.mpr hRMinimal, hyR, hRS, ?_⟩
  intro z hzR hzA
  have hzS := hRS hzR
  simp only [S, Finset.mem_insert, Finset.mem_erase] at hzS
  rcases hzS with hzy | ⟨-, hzA'⟩
  · exact hzy
  · exact (hzA hzA').elim

theorem four_le_card_of_four_mem {α : Type*}
    {F : Hypergraph α} {A B C D : Row α}
    (hAF : A ∈ F) (hBF : B ∈ F) (hCF : C ∈ F) (hDF : D ∈ F)
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) :
    4 ≤ F.card := by
  classical
  have hSubset : ({A, B, C, D} : Hypergraph α) ⊆ F := by
    intro E hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact hAF
    · exact hBF
    · exact hCF
    · exact hDF
  have hCard := Finset.card_le_card hSubset
  simpa [hAB, hAC, hAD, hBC, hBD, hCD] using hCard

theorem four_blockers_of_distinct_replacements {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ A : Row α} {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hK : K = {T₁, T₂, T₃})
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hPrivate₁ : IsPrivateRowFor K A x₁ T₁)
    (hPrivate₂ : IsPrivateRowFor K A x₂ T₂)
    (hPrivate₃ : IsPrivateRowFor K A x₃ T₃)
    (hAb : A ∈ blocker K)
    (hy₁T₁ : y₁ ∈ T₁) (hy₂T₂ : y₂ ∈ T₂) (hy₃T₃ : y₃ ∈ T₃)
    (hy₁A : y₁ ∉ A) (hy₂A : y₂ ∉ A) (hy₃A : y₃ ∉ A)
    (hy₁y₂ : y₁ ≠ y₂) (hy₁y₃ : y₁ ≠ y₃) (hy₂y₃ : y₂ ≠ y₃) :
    4 ≤ (blocker K).card := by
  obtain ⟨R₁, hR₁b, hy₁R₁, hR₁S, hR₁Outside⟩ :=
    exists_replacement_blocker_threeRows hK hx₁x₂ hx₁x₃
      hPrivate₁ hPrivate₂ hPrivate₃ hy₁T₁ hy₁A
  obtain ⟨R₂, hR₂b, hy₂R₂, hR₂S, hR₂Outside⟩ :=
    exists_replacement_blocker_threeRows (by
      rw [hK]
      ext T
      simp [or_left_comm]) hx₁x₂.symm hx₂x₃
      hPrivate₂ hPrivate₁ hPrivate₃ hy₂T₂ hy₂A
  obtain ⟨R₃, hR₃b, hy₃R₃, hR₃S, hR₃Outside⟩ :=
    exists_replacement_blocker_threeRows (by
      rw [hK]
      ext T
      simp [or_comm, or_left_comm])
      hx₁x₃.symm hx₂x₃.symm hPrivate₃ hPrivate₁ hPrivate₂ hy₃T₃ hy₃A
  have hAR₁ : A ≠ R₁ := fun hEq ↦ hy₁A (hEq ▸ hy₁R₁)
  have hAR₂ : A ≠ R₂ := fun hEq ↦ hy₂A (hEq ▸ hy₂R₂)
  have hAR₃ : A ≠ R₃ := fun hEq ↦ hy₃A (hEq ▸ hy₃R₃)
  have hR₁R₂ : R₁ ≠ R₂ := by
    intro hEq
    have hy₁R₂ : y₁ ∈ R₂ := hEq ▸ hy₁R₁
    exact hy₁y₂ (hR₂Outside y₁ hy₁R₂ hy₁A)
  have hR₁R₃ : R₁ ≠ R₃ := by
    intro hEq
    have hy₁R₃ : y₁ ∈ R₃ := hEq ▸ hy₁R₁
    exact hy₁y₃ (hR₃Outside y₁ hy₁R₃ hy₁A)
  have hR₂R₃ : R₂ ≠ R₃ := by
    intro hEq
    have hy₂R₃ : y₂ ∈ R₃ := hEq ▸ hy₂R₂
    exact hy₂y₃ (hR₃Outside y₂ hy₂R₃ hy₂A)
  exact four_le_card_of_four_mem hAb hR₁b hR₂b hR₃b
    hAR₁ hAR₂ hAR₃ hR₁R₂ hR₁R₃ hR₂R₃

theorem four_blockers_of_shared_replacements {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ A : Row α} {x₁ x₂ x₃ y z : α}
    (hK : K = {T₁, T₂, T₃})
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hPrivate₁ : IsPrivateRowFor K A x₁ T₁)
    (hPrivate₂ : IsPrivateRowFor K A x₂ T₂)
    (hPrivate₃ : IsPrivateRowFor K A x₃ T₃)
    (hAb : A ∈ blocker K)
    (hyT₁ : y ∈ T₁) (hyT₂ : y ∈ T₂) (hyT₃ : y ∉ T₃)
    (hzT₃ : z ∈ T₃) (hzMiss : z ∉ T₁ ∨ z ∉ T₂)
    (hyA : y ∉ A) (hzA : z ∉ A) (hyz : y ≠ z) :
    4 ≤ (blocker K).card := by
  obtain ⟨Rᵧ, hRᵧb, hyRᵧ, -, hRᵧOutside⟩ :=
    exists_replacement_blocker_threeRows hK hx₁x₂ hx₁x₃
      hPrivate₁ hPrivate₂ hPrivate₃ hyT₁ hyA
  obtain ⟨Rz, hRzb, hzRz, -, hRzOutside⟩ :=
    exists_replacement_blocker_threeRows (by
      rw [hK]
      ext T
      simp [or_comm, or_left_comm])
      hx₁x₃.symm hx₂x₃.symm hPrivate₃ hPrivate₁ hPrivate₂ hzT₃ hzA
  have hPairTransversal : IsTransversal K {y, z} := by
    intro T hTK
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hTK
    rcases hTK with rfl | rfl | rfl
    · exact ⟨y, by simp, hyT₁⟩
    · exact ⟨y, by simp, hyT₂⟩
    · exact ⟨z, by simp, hzT₃⟩
  have hPairMinimal : IsMinimalTransversal K {y, z} := by
    apply hPairTransversal.minimal_of_privateRows
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · rcases hzMiss with hzT₁ | hzT₂
      · exact ⟨T₁, hPrivate₁.1, by simp, hyT₁, by
          intro w hwPair hwT₁
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwPair
          rcases hwPair with rfl | rfl
          · rfl
          · exact (hzT₁ hwT₁).elim⟩
      · exact ⟨T₂, hPrivate₂.1, by simp, hyT₂, by
          intro w hwPair hwT₂
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwPair
          rcases hwPair with rfl | rfl
          · rfl
          · exact (hzT₂ hwT₂).elim⟩
    · exact ⟨T₃, hPrivate₃.1, by simp, hzT₃, by
        intro w hwPair hwT₃
        simp only [Finset.mem_insert, Finset.mem_singleton] at hwPair
        rcases hwPair with rfl | rfl
        · exact (hyT₃ hwT₃).elim
        · rfl⟩
  have hPairb : ({y, z} : Row α) ∈ blocker K := mem_blocker.mpr hPairMinimal
  have hARᵧ : A ≠ Rᵧ := fun hEq ↦ hyA (hEq ▸ hyRᵧ)
  have hARz : A ≠ Rz := fun hEq ↦ hzA (hEq ▸ hzRz)
  have hAPair : A ≠ {y, z} := by
    intro hEq
    have hyA' : y ∈ A := by rw [hEq]; simp
    exact hyA hyA'
  have hRᵧRz : Rᵧ ≠ Rz := by
    intro hEq
    have hyRz : y ∈ Rz := hEq ▸ hyRᵧ
    exact hyz (hRzOutside y hyRz hyA)
  have hRᵧPair : Rᵧ ≠ {y, z} := by
    intro hEq
    have hzRᵧ : z ∈ Rᵧ := by rw [hEq]; simp
    exact hyz (hRᵧOutside z hzRᵧ hzA).symm
  have hRzPair : Rz ≠ {y, z} := by
    intro hEq
    have hyRz : y ∈ Rz := by rw [hEq]; simp
    exact hyz (hRzOutside y hyRz hyA)
  exact four_le_card_of_four_mem hAb hRᵧb hRzb hPairb
    hARᵧ hARz hAPair hRᵧRz hRᵧPair hRzPair

theorem threeRow_blocker_eq_three_rows_are_pairs {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHcard : H.card = 3)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hBcard : (blocker H).card = 3) :
    ∀ E ∈ H, E.card = 2 := by
  classical
  intro A hAH
  have hAdual : A ∈ blocker (blocker H) := by
    rw [blocker_involution hH]
    exact hAH
  have hAupper : A.card ≤ 3 := by
    have := minimalTransversal_card_le_rows (mem_blocker.mp hAdual)
    omega
  have hAlower := hHRows A hAH
  by_contra hAcardNotTwo
  have hAcard : A.card = 3 := by omega
  obtain ⟨x₁, x₂, x₃, hx₁x₂, hx₁x₃, hx₂x₃, hA⟩ := Finset.card_eq_three.mp hAcard
  have hx₁A : x₁ ∈ A := by simp [hA]
  have hx₂A : x₂ ∈ A := by simp [hA]
  have hx₃A : x₃ ∈ A := by simp [hA]
  obtain ⟨T₁, hT₁b, hWitness₁⟩ := exists_blocker_private_at_row hH hAH hx₁A
  obtain ⟨T₂, hT₂b, hWitness₂⟩ := exists_blocker_private_at_row hH hAH hx₂A
  obtain ⟨T₃, hT₃b, hWitness₃⟩ := exists_blocker_private_at_row hH hAH hx₃A
  have hT₁T₂ : T₁ ≠ T₂ := by
    intro hEq
    have hx₂T₁ : x₂ ∈ T₁ := by rw [hEq]; exact hWitness₂.2.1
    have hx₂x₁ : x₂ = x₁ := hWitness₁.2.2.2 hx₂T₁ hx₂A
    exact hx₁x₂ hx₂x₁.symm
  have hT₁T₃ : T₁ ≠ T₃ := by
    intro hEq
    have hx₃T₁ : x₃ ∈ T₁ := by rw [hEq]; exact hWitness₃.2.1
    have hx₃x₁ : x₃ = x₁ := hWitness₁.2.2.2 hx₃T₁ hx₃A
    exact hx₁x₃ hx₃x₁.symm
  have hT₂T₃ : T₂ ≠ T₃ := by
    intro hEq
    have hx₃T₂ : x₃ ∈ T₂ := by rw [hEq]; exact hWitness₃.2.1
    have hx₃x₂ : x₃ = x₂ := hWitness₂.2.2.2 hx₃T₂ hx₃A
    exact hx₂x₃ hx₃x₂.symm
  have hK : blocker H = {T₁, T₂, T₃} := by
    have hSubset : ({T₁, T₂, T₃} : Hypergraph α) ⊆ blocker H := by
      intro T hT
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl
      · exact hT₁b
      · exact hT₂b
      · exact hT₃b
    exact (Finset.eq_of_subset_of_card_le hSubset (by
      simpa [hT₁T₂, hT₁T₃, hT₂T₃] using hBcard.le)).symm
  have hPrivate₁ : IsPrivateRowFor (blocker H) A x₁ T₁ :=
    ⟨hT₁b, hx₁A, hWitness₁.2.1, fun _ hyA hyT₁ ↦
      hWitness₁.2.2.2 hyT₁ hyA⟩
  have hPrivate₂ : IsPrivateRowFor (blocker H) A x₂ T₂ :=
    ⟨hT₂b, hx₂A, hWitness₂.2.1, fun _ hyA hyT₂ ↦
      hWitness₂.2.2.2 hyT₂ hyA⟩
  have hPrivate₃ : IsPrivateRowFor (blocker H) A x₃ T₃ :=
    ⟨hT₃b, hx₃A, hWitness₃.2.1, fun _ hyA hyT₃ ↦
      hWitness₃.2.2.2 hyT₃ hyA⟩
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 2 := by
    rw [blocker_involution hH]
    exact hHRows
  have hNoCommon :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hK hDualRows
  obtain ⟨y₁, hy₁T₁, hy₁x₁⟩ := Finset.exists_mem_ne (s := T₁) (by
    have := hBRows T₁ hT₁b
    omega) x₁
  obtain ⟨y₂, hy₂T₂, hy₂x₂⟩ := Finset.exists_mem_ne (s := T₂) (by
    have := hBRows T₂ hT₂b
    omega) x₂
  obtain ⟨y₃, hy₃T₃, hy₃x₃⟩ := Finset.exists_mem_ne (s := T₃) (by
    have := hBRows T₃ hT₃b
    omega) x₃
  have hy₁A : y₁ ∉ A := fun hyA ↦ hy₁x₁ (hPrivate₁.2.2.2 hyA hy₁T₁)
  have hy₂A : y₂ ∉ A := fun hyA ↦ hy₂x₂ (hPrivate₂.2.2.2 hyA hy₂T₂)
  have hy₃A : y₃ ∉ A := fun hyA ↦ hy₃x₃ (hPrivate₃.2.2.2 hyA hy₃T₃)
  have hAb : A ∈ blocker (blocker H) := hAdual
  have hFour : 4 ≤ (blocker (blocker H)).card := by
    by_cases hy₁y₂ : y₁ = y₂
    · subst y₂
      have hy₁T₃ : y₁ ∉ T₃ := fun hy₁T₃ ↦ hNoCommon y₁ ⟨hy₁T₁, hy₂T₂, hy₁T₃⟩
      have hy₃Miss : y₃ ∉ T₁ ∨ y₃ ∉ T₂ := by
        by_contra hnot
        push Not at hnot
        exact hNoCommon y₃ ⟨hnot.1, hnot.2, hy₃T₃⟩
      have hy₁y₃ : y₁ ≠ y₃ := fun hEq ↦ hy₁T₃ (hEq ▸ hy₃T₃)
      exact four_blockers_of_shared_replacements hK hx₁x₂ hx₁x₃ hx₂x₃
        hPrivate₁ hPrivate₂ hPrivate₃ hAb hy₁T₁ hy₂T₂ hy₁T₃ hy₃T₃
        hy₃Miss hy₁A hy₃A hy₁y₃
    · by_cases hy₁y₃ : y₁ = y₃
      · subst y₃
        have hy₁T₂ : y₁ ∉ T₂ := fun hy₁T₂ ↦ hNoCommon y₁ ⟨hy₁T₁, hy₁T₂, hy₃T₃⟩
        have hy₂Miss : y₂ ∉ T₁ ∨ y₂ ∉ T₃ := by
          by_contra hnot
          push Not at hnot
          exact hNoCommon y₂ ⟨hnot.1, hy₂T₂, hnot.2⟩
        have hy₁y₂' : y₁ ≠ y₂ := hy₁y₂
        exact four_blockers_of_shared_replacements
          (by
            rw [hK]
            ext T
            simp [or_comm])
          hx₁x₃ hx₁x₂ hx₂x₃.symm hPrivate₁ hPrivate₃ hPrivate₂ hAb
          hy₁T₁ hy₃T₃ hy₁T₂ hy₂T₂ hy₂Miss hy₁A hy₂A hy₁y₂'
      · by_cases hy₂y₃ : y₂ = y₃
        · subst y₃
          have hy₂T₁ : y₂ ∉ T₁ := fun hy₂T₁ ↦ hNoCommon y₂ ⟨hy₂T₁, hy₂T₂, hy₃T₃⟩
          have hy₁Miss : y₁ ∉ T₂ ∨ y₁ ∉ T₃ := by
            by_contra hnot
            push Not at hnot
            exact hNoCommon y₁ ⟨hy₁T₁, hnot.1, hnot.2⟩
          exact four_blockers_of_shared_replacements
            (by
              rw [hK]
              ext T
              simp [or_comm, or_left_comm])
            hx₂x₃ hx₁x₂.symm hx₁x₃.symm hPrivate₂ hPrivate₃ hPrivate₁ hAb
            hy₂T₂ hy₃T₃ hy₂T₁ hy₁T₁ hy₁Miss hy₂A hy₁A (Ne.symm hy₁y₂)
        · exact four_blockers_of_distinct_replacements hK
            hx₁x₂ hx₁x₃ hx₂x₃ hPrivate₁ hPrivate₂ hPrivate₃ hAb
            hy₁T₁ hy₂T₂ hy₃T₃ hy₁A hy₂A hy₃A hy₁y₂ hy₁y₃ hy₂y₃
  rw [blocker_involution hH, hHcard] at hFour
  omega

theorem threeRow_pairRows_card_eq_three_of_blocker_card_eq_three {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHcard : H.card = 3)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hBcard : (blocker H).card = 3) :
    (pairRows H).card = 3 := by
  classical
  have hRows := threeRow_blocker_eq_three_rows_are_pairs hH hHcard hHRows hBRows hBcard
  have hPairRows : pairRows H = H := by
    ext E
    simp only [pairRows, Finset.mem_filter]
    constructor
    · exact fun hE ↦ hE.1
    · intro hEH
      exact ⟨hEH, hRows E hEH⟩
  rw [hPairRows, hHcard]

theorem threeRow_blocker_card_ge_four_of_pairRows_card_le_two {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) (hHcard : H.card = 3)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 2)
    (hPairs : (pairRows H).card ≤ 2) :
    4 ≤ (blocker H).card := by
  classical
  have hThree := threeRow_blocker_card_ge_three hH hHcard hHRows hBRows
  by_contra hnot
  have hBcard : (blocker H).card = 3 := by omega
  have hPairCard :=
    threeRow_pairRows_card_eq_three_of_blocker_card_eq_three
      hH hHcard hHRows hBRows hBcard
  omega

theorem first_two_rows_disjoint_of_threeRows_blocker_rows_cardAtLeast_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃}) (hKRows : RowsCardAtLeast K 2)
    (hBRows : RowsCardAtLeast (blocker K) 3) :
    Disjoint T₁ T₂ := by
  apply Finset.disjoint_left.mpr
  intro x hxT₁ hxT₂
  have hT₃K : T₃ ∈ K := by simp [hK]
  have hT₃positive : 0 < T₃.card := by
    have := hKRows T₃ hT₃K
    omega
  obtain ⟨y, hyT₃⟩ := Finset.card_pos.mp hT₃positive
  have hPairTransversal : IsTransversal K {x, y} := by
    intro T hTK
    simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hTK
    rcases hTK with rfl | rfl | rfl
    · exact ⟨x, by simp, hxT₁⟩
    · exact ⟨x, by simp, hxT₂⟩
    · exact ⟨y, by simp, hyT₃⟩
  obtain ⟨S, hSPair, hSMinimal⟩ := exists_minimalTransversal_subset hPairTransversal
  have hSBlocker : S ∈ blocker K := mem_blocker.mpr hSMinimal
  have hSupper : S.card ≤ 2 :=
    (Finset.card_le_card hSPair).trans Finset.card_le_two
  have hSlower := hBRows S hSBlocker
  omega

theorem threeRows_pairwise_disjoint_of_blocker_rows_cardAtLeast_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃}) (hKRows : RowsCardAtLeast K 2)
    (hBRows : RowsCardAtLeast (blocker K) 3) :
    Disjoint T₁ T₂ ∧ Disjoint T₁ T₃ ∧ Disjoint T₂ T₃ := by
  refine ⟨first_two_rows_disjoint_of_threeRows_blocker_rows_cardAtLeast_three
    hK hKRows hBRows, ?_, ?_⟩
  · exact first_two_rows_disjoint_of_threeRows_blocker_rows_cardAtLeast_three
      (T₁ := T₁) (T₂ := T₃) (T₃ := T₂)
      (by
        rw [hK]
        ext T
        simp [or_comm]) hKRows hBRows
  · exact first_two_rows_disjoint_of_threeRows_blocker_rows_cardAtLeast_three
      (T₁ := T₂) (T₂ := T₃) (T₃ := T₁)
      (by
        rw [hK]
        ext T
        simp [or_comm, or_left_comm]) hKRows hBRows

theorem card_mul_mul_le_threeRow_blocker_card_of_pairwise_disjoint {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : Hypergraph α} {T₁ T₂ T₃ : Row α}
    (hK : K = {T₁, T₂, T₃})
    (h₁₂ : Disjoint T₁ T₂) (h₁₃ : Disjoint T₁ T₃) (h₂₃ : Disjoint T₂ T₃) :
    T₁.card * T₂.card * T₃.card ≤ (blocker K).card := by
  let tripleRow : (α × α) × α → Row α := fun p ↦ {p.1.1, p.1.2, p.2}
  let choices : Finset ((α × α) × α) := (T₁.product T₂).product T₃
  have hInjective : Set.InjOn tripleRow (↑choices : Set ((α × α) × α)) := by
    intro p hp q hq hEq
    have hp' : p ∈ choices := hp
    have hq' : q ∈ choices := hq
    obtain ⟨hpPair, hp₃⟩ := Finset.mem_product.mp hp'
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpPair
    obtain ⟨hqPair, hq₃⟩ := Finset.mem_product.mp hq'
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hqPair
    apply Prod.ext
    · apply Prod.ext
      · have hpMem : p.1.1 ∈ tripleRow q := by
          rw [← hEq]
          simp [tripleRow]
        simp only [tripleRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
        rcases hpMem with hpq | hpq | hpq
        · exact hpq
        · exact (Finset.disjoint_left.mp h₁₂ hp₁ (hpq ▸ hq₂)).elim
        · exact (Finset.disjoint_left.mp h₁₃ hp₁ (hpq ▸ hq₃)).elim
      · have hpMem : p.1.2 ∈ tripleRow q := by
          rw [← hEq]
          simp [tripleRow]
        simp only [tripleRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
        rcases hpMem with hpq | hpq | hpq
        · exact (Finset.disjoint_left.mp h₁₂ (hpq ▸ hq₁) hp₂).elim
        · exact hpq
        · exact (Finset.disjoint_left.mp h₂₃ hp₂ (hpq ▸ hq₃)).elim
    · have hpMem : p.2 ∈ tripleRow q := by
        rw [← hEq]
        simp [tripleRow]
      simp only [tripleRow, Finset.mem_insert, Finset.mem_singleton] at hpMem
      rcases hpMem with hpq | hpq | hpq
      · exact (Finset.disjoint_left.mp h₁₃ (hpq ▸ hq₁) hp₃).elim
      · exact (Finset.disjoint_left.mp h₂₃ (hpq ▸ hq₂) hp₃).elim
      · exact hpq
  have hImageSubset : choices.image tripleRow ⊆ blocker K := by
    intro E hE
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hpPair, hp₃⟩ := Finset.mem_product.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpPair
    apply mem_blocker.mpr
    have hTransversal : IsTransversal K (tripleRow p) := by
      intro T hTK
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hTK
      rcases hTK with rfl | rfl | rfl
      · exact ⟨p.1.1, by simp [tripleRow], hp₁⟩
      · exact ⟨p.1.2, by simp [tripleRow], hp₂⟩
      · exact ⟨p.2, by simp [tripleRow], hp₃⟩
    apply hTransversal.minimal_of_privateRows
    intro x hx
    simp only [tripleRow, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨T₁, by simp [hK], by simp [tripleRow], hp₁, by
        intro y hyTriple hyT₁
        simp only [tripleRow, Finset.mem_insert, Finset.mem_singleton] at hyTriple
        rcases hyTriple with rfl | rfl | rfl
        · rfl
        · exact (Finset.disjoint_left.mp h₁₂ hyT₁ hp₂).elim
        · exact (Finset.disjoint_left.mp h₁₃ hyT₁ hp₃).elim⟩
    · exact ⟨T₂, by simp [hK], by simp [tripleRow], hp₂, by
        intro y hyTriple hyT₂
        simp only [tripleRow, Finset.mem_insert, Finset.mem_singleton] at hyTriple
        rcases hyTriple with rfl | rfl | rfl
        · exact (Finset.disjoint_left.mp h₁₂ hp₁ hyT₂).elim
        · rfl
        · exact (Finset.disjoint_left.mp h₂₃ hyT₂ hp₃).elim⟩
    · exact ⟨T₃, by simp [hK], by simp [tripleRow], hp₃, by
        intro y hyTriple hyT₃
        simp only [tripleRow, Finset.mem_insert, Finset.mem_singleton] at hyTriple
        rcases hyTriple with rfl | rfl | rfl
        · exact (Finset.disjoint_left.mp h₁₃ hp₁ hyT₃).elim
        · exact (Finset.disjoint_left.mp h₂₃ hp₂ hyT₃).elim
        · rfl⟩
  calc
    T₁.card * T₂.card * T₃.card = choices.card := by
      simp [choices, Finset.card_product]
    _ = (choices.image tripleRow).card :=
      (Finset.card_image_iff.mpr hInjective).symm
    _ ≤ (blocker K).card := Finset.card_le_card hImageSubset

theorem threeRow_blocker_card_ge_eight_of_rows_cardAtLeast_three {α : Type*}
    [Fintype α]
    {H : Hypergraph α} (hHcard : H.card = 3)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    8 ≤ (blocker H).card := by
  classical
  obtain ⟨T₁, T₂, T₃, hT₁T₂, hT₁T₃, hT₂T₃, hH⟩ := Finset.card_eq_three.mp hHcard
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ :=
    threeRows_pairwise_disjoint_of_blocker_rows_cardAtLeast_three hH hHRows hBRows
  have hProduct := card_mul_mul_le_threeRow_blocker_card_of_pairwise_disjoint
    hH h₁₂ h₁₃ h₂₃
  have hT₁H : T₁ ∈ H := by simp [hH]
  have hT₂H : T₂ ∈ H := by simp [hH]
  have hT₃H : T₃ ∈ H := by simp [hH]
  calc
    8 = 2 * 2 * 2 := rfl
    _ ≤ T₁.card * T₂.card * T₃.card :=
      Nat.mul_le_mul (Nat.mul_le_mul (hHRows T₁ hT₁H) (hHRows T₂ hT₂H))
        (hHRows T₃ hT₃H)
    _ ≤ (blocker H).card := hProduct

end AiMathLab.P0054.G413
