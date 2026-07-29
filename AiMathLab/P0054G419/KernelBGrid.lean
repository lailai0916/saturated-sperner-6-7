import AiMathLab.P0054G419.KernelBStar

namespace AiMathLab.P0054.G419

open G413

theorem tripleChoiceRows_all_first {α : Type*}
    [DecidableEq α]
    {a : α} {A B C : Row α} {F : G413.Hypergraph α}
    (hA : A = {a}) (hF : F ⊆ tripleChoiceRows A B C) :
    ∀ E ∈ F, a ∈ E := by
  intro E hEF
  obtain ⟨p, hpA, q, hqB, r, hrC, hpqr⟩ :=
    mem_tripleChoiceRows.mp (hF hEF)
  have hpa : p = a := by rw [hA] at hpA; simpa using hpA
  rw [← hpqr, hpa]
  simp

theorem tripleChoiceRows_second_mem_blocker_of_card_ge_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {A B C : Row α} {F : G413.Hypergraph α}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hACard : A.card = 1) (hBCard : B.card = 2) (hCCard : C.card = 2)
    (hFSubset : F ⊆ tripleChoiceRows A B C) (hFCard : 3 ≤ F.card) :
    B ∈ blocker F := by
  classical
  have hBTransversal : IsTransversal F B := by
    intro E hEF
    obtain ⟨a, haA, b, hbB, c, hcC, habc⟩ :=
      mem_tripleChoiceRows.mp (hFSubset hEF)
    exact ⟨b, hbB, by rw [← habc]; simp⟩
  apply mem_blocker.mpr
  apply hBTransversal.minimal_of_privateRows
  intro b hbB
  have hExists : ∃ E ∈ F, b ∈ E := by
    by_contra h
    push Not at h
    have hFSmall : F ⊆ tripleChoiceRows A (B.erase b) C := by
      intro E hEF
      obtain ⟨a, haA, q, hqB, c, hcC, haqc⟩ :=
        mem_tripleChoiceRows.mp (hFSubset hEF)
      have hqb : q ≠ b := by
        intro hqb
        apply h E hEF
        rw [← haqc, hqb]
        simp
      exact mem_tripleChoiceRows.mpr
        ⟨a, haA, q, Finset.mem_erase.mpr ⟨hqb, hqB⟩, c, hcC, haqc⟩
    have hAEraseB : Disjoint A (B.erase b) :=
      hAB.mono_right (Finset.erase_subset b B)
    have hEraseBC : Disjoint (B.erase b) C :=
      hBC.mono_left (Finset.erase_subset b B)
    have hEraseCard : (B.erase b).card = 1 := by
      rw [Finset.card_erase_of_mem hbB, hBCard]
    have hFamilyCard : (tripleChoiceRows A (B.erase b) C).card = 2 := by
      rw [tripleChoiceRows_card hAEraseB hAC hEraseBC,
        hACard, hEraseCard, hCCard]
    have hCardUpper := Finset.card_le_card hFSmall
    rw [hFamilyCard] at hCardUpper
    omega
  obtain ⟨E, hEF, hbE⟩ := hExists
  refine ⟨E, hEF, hbB, hbE, ?_⟩
  intro y hyB hyE
  obtain ⟨a, haA, q, hqB, c, hcC, haqc⟩ :=
    mem_tripleChoiceRows.mp (hFSubset hEF)
  have hbRow : b = a ∨ b = q ∨ b = c := by
    have : b ∈ ({a, q, c} : Row α) := by rw [haqc]; exact hbE
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hyRow : y = a ∨ y = q ∨ y = c := by
    have : y ∈ ({a, q, c} : Row α) := by rw [haqc]; exact hyE
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hba : b ≠ a := by
    intro hba
    subst a
    exact Finset.disjoint_left.mp hAB haA hbB
  have hbc : b ≠ c := by
    intro hbc
    subst c
    exact Finset.disjoint_left.mp hBC hbB hcC
  have hya : y ≠ a := by
    intro hya
    subst a
    exact Finset.disjoint_left.mp hAB haA hyB
  have hyc : y ≠ c := by
    intro hyc
    subst c
    exact Finset.disjoint_left.mp hBC hyB hcC
  have hbq : b = q := by rcases hbRow with h | h | h <;> tauto
  have hyq : y = q := by rcases hyRow with h | h | h <;> tauto
  exact hyq.trans hbq.symm

theorem tripleChoiceRows_swap_last {α : Type*} [DecidableEq α]
    (A B C : Row α) :
    tripleChoiceRows A B C = tripleChoiceRows A C B := by
  classical
  ext E
  constructor
  · intro hE
    obtain ⟨a, haA, b, hbB, c, hcC, habc⟩ := mem_tripleChoiceRows.mp hE
    exact mem_tripleChoiceRows.mpr
      ⟨a, haA, c, hcC, b, hbB, by simpa [Finset.pair_comm] using habc⟩
  · intro hE
    obtain ⟨a, haA, c, hcC, b, hbB, hacb⟩ := mem_tripleChoiceRows.mp hE
    exact mem_tripleChoiceRows.mpr
      ⟨a, haA, b, hbB, c, hcC, by simpa [Finset.pair_comm] using hacb⟩

theorem tripleChoiceRows_two_covers_of_card_ge_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {A B C : Row α} {F : G413.Hypergraph α}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hACard : A.card = 1) (hBCard : B.card = 2) (hCCard : C.card = 2)
    (hFSubset : F ⊆ tripleChoiceRows A B C) (hFCard : 3 ≤ F.card) :
    B ∈ blocker F ∧ C ∈ blocker F := by
  constructor
  · exact tripleChoiceRows_second_mem_blocker_of_card_ge_three
      hAB hAC hBC hACard hBCard hCCard hFSubset hFCard
  · apply tripleChoiceRows_second_mem_blocker_of_card_ge_three
      hAC hAB hBC.symm hACard hCCard hBCard
    · intro E hEF
      rw [← tripleChoiceRows_swap_last A B C]
      exact hFSubset hEF
    · exact hFCard

end AiMathLab.P0054.G419
