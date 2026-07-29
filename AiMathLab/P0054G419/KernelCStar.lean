import AiMathLab.P0054G419.KernelC

namespace AiMathLab.P0054.G419

open G413

noncomputable def threeStarRows {α : Type*} [DecidableEq α]
    (a b : α) (C : Row α) : G413.Hypergraph α := by
  classical
  exact C.image fun c ↦ {a, b, c}

@[simp]
theorem mem_threeStarRows {α : Type*} [DecidableEq α]
    {a b : α} {C E : Row α} :
    E ∈ threeStarRows a b C ↔ ∃ c ∈ C, {a, b, c} = E := by
  classical
  simp [threeStarRows]

theorem exists_mem_ne_of_card_three {α : Type*}
    {C : Row α} (hC : C.card = 3) (q : α) :
    ∃ c ∈ C, c ≠ q := by
  have hTwo : 1 < C.card := by omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hTwo
  by_cases hcq : c = q
  · exact ⟨d, hd, fun hdq ↦ hcd (hcq.trans hdq.symm)⟩
  · exact ⟨c, hc, hcq⟩

theorem first_star_pair_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {a b q : α} {C Q : Row α} {T : G413.Hypergraph α}
    (hT : T = insert Q (threeStarRows a b C))
    (hC : C.card = 3)
    (hqQ : q ∈ Q) (haQ : a ∉ Q) (hbQ : b ∉ Q) :
    ({a, q} : Row α) ∈ blocker T := by
  have haq : a ≠ q := fun haq ↦ haQ (haq ▸ hqQ)
  have hTransversal : IsTransversal T {a, q} := by
    intro E hET
    rw [hT] at hET
    simp only [Finset.mem_insert] at hET
    rcases hET with rfl | hEStar
    · exact ⟨q, by simp, hqQ⟩
    · obtain ⟨c, hcC, rfl⟩ := mem_threeStarRows.mp hEStar
      exact ⟨a, by simp, by simp⟩
  apply mem_blocker.mpr
  apply hTransversal.minimal_of_privateRows
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hza | hzq
  · subst z
    obtain ⟨c, hcC, hcq⟩ := exists_mem_ne_of_card_three hC q
    refine ⟨{a, b, c}, ?_, by simp, by simp, ?_⟩
    · rw [hT]
      exact Finset.mem_insert_of_mem (mem_threeStarRows.mpr ⟨c, hcC, rfl⟩)
    · intro y hyPair hyRow
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyPair hyRow
      rcases hyPair with hya | hyq
      · exact hya
      · subst y
        rcases hyRow with hqa | hqb | hqc
        · exact (haq hqa.symm).elim
        · exact (hbQ (hqb ▸ hqQ)).elim
        · exact (hcq hqc.symm).elim
  · subst z
    refine ⟨Q, by rw [hT]; simp, by simp, hqQ, ?_⟩
    intro y hyPair hyQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyPair
    rcases hyPair with hya | hyq
    · exact (haQ (hya ▸ hyQ)).elim
    · exact hyq

theorem second_star_pair_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α]
    {a b q : α} {C Q : Row α} {T : G413.Hypergraph α}
    (hT : T = insert Q (threeStarRows a b C))
    (hC : C.card = 3)
    (hab : a ≠ b)
    (hqQ : q ∈ Q) (haQ : a ∉ Q) (hbQ : b ∉ Q) :
    ({b, q} : Row α) ∈ blocker T := by
  have hba : b ≠ a := hab.symm
  have hbq : b ≠ q := fun hbq ↦ hbQ (hbq ▸ hqQ)
  have hTransversal : IsTransversal T {b, q} := by
    intro E hET
    rw [hT] at hET
    simp only [Finset.mem_insert] at hET
    rcases hET with rfl | hEStar
    · exact ⟨q, by simp, hqQ⟩
    · obtain ⟨c, hcC, rfl⟩ := mem_threeStarRows.mp hEStar
      exact ⟨b, by simp, by simp⟩
  apply mem_blocker.mpr
  apply hTransversal.minimal_of_privateRows
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hzb | hzq
  · subst z
    obtain ⟨c, hcC, hcq⟩ := exists_mem_ne_of_card_three hC q
    refine ⟨{a, b, c}, ?_, by simp, by simp, ?_⟩
    · rw [hT]
      exact Finset.mem_insert_of_mem (mem_threeStarRows.mpr ⟨c, hcC, rfl⟩)
    · intro y hyPair hyRow
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyPair hyRow
      rcases hyPair with hyb | hyq
      · exact hyb
      · subst y
        rcases hyRow with hqa | hqb | hqc
        · exact (haQ (hqa ▸ hqQ)).elim
        · exact (hbq hqb.symm).elim
        · exact (hcq hqc.symm).elim
  · subst z
    refine ⟨Q, by rw [hT]; simp, by simp, hqQ, ?_⟩
    intro y hyPair hyQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyPair
    rcases hyPair with hyb | hyq
    · exact (hbQ (hyb ▸ hyQ)).elim
    · exact hyq

theorem kernelC_star_blocker_card_ge_seven {α : Type*}
    [Fintype α] [DecidableEq α]
    {a b : α} {C Q : Row α} {T : G413.Hypergraph α}
    (hT : T = insert Q (threeStarRows a b C))
    (hC : C.card = 3)
    (hab : a ≠ b) (haC : a ∉ C) (hbC : b ∉ C)
    (hTRows : RowsCardAtLeast T 3)
    (hBRows : RowsCardAtLeast (blocker T) 2) :
    7 ≤ (blocker T).card := by
  classical
  have hQT : Q ∈ T := by rw [hT]; simp
  have hQCard : 3 ≤ Q.card := hTRows Q hQT
  have haQ : a ∉ Q := by
    intro haQ
    have hTransversal : IsTransversal T {a} := by
      intro E hET
      rw [hT] at hET
      simp only [Finset.mem_insert] at hET
      rcases hET with rfl | hEStar
      · exact ⟨a, by simp, haQ⟩
      · obtain ⟨c, hcC, rfl⟩ := mem_threeStarRows.mp hEStar
        exact ⟨a, by simp, by simp⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  have hbQ : b ∉ Q := by
    intro hbQ
    have hTransversal : IsTransversal T {b} := by
      intro E hET
      rw [hT] at hET
      simp only [Finset.mem_insert] at hET
      rcases hET with rfl | hEStar
      · exact ⟨b, by simp, hbQ⟩
      · obtain ⟨c, hcC, rfl⟩ := mem_threeStarRows.mp hEStar
        exact ⟨b, by simp, by simp⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  let pairs := crossPairRows ({a, b} : Row α) Q
  have hPairSubset : pairs ⊆ blocker T := by
    intro E hE
    obtain ⟨s, hs, q, hqQ, rfl⟩ := mem_crossPairRows.mp hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact first_star_pair_mem_blocker hT hC hqQ haQ hbQ
    · exact second_star_pair_mem_blocker hT hC hab hqQ haQ hbQ
  have hPairDisjoint : Disjoint ({a, b} : Row α) Q := by
    apply Finset.disjoint_left.mpr
    intro s hs hsQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact haQ hsQ
    · exact hbQ hsQ
  have hPairLower : 6 ≤ pairs.card := by
    have hFirstCard : ({a, b} : Row α).card = 2 := by simp [hab]
    calc
      6 ≤ ({a, b} : Row α).card * Q.card := by rw [hFirstCard]; omega
      _ ≤ pairs.card := card_mul_le_crossPairRows_card_of_disjoint hPairDisjoint
  have hExtra : ∃ S ∈ blocker T, S.card ≠ 2 := by
    by_cases hMeet : (Q ∩ C).Nonempty
    · obtain ⟨d, hdMeet⟩ := hMeet
      obtain ⟨hdQ, hdC⟩ := Finset.mem_inter.mp hdMeet
      have hCTransversal : IsTransversal T C := by
        intro E hET
        rw [hT] at hET
        simp only [Finset.mem_insert] at hET
        rcases hET with rfl | hEStar
        · exact ⟨d, hdC, hdQ⟩
        · obtain ⟨c, hcC, rfl⟩ := mem_threeStarRows.mp hEStar
          exact ⟨c, hcC, by simp⟩
      have hCBlocker : C ∈ blocker T := by
        apply mem_blocker.mpr
        apply hCTransversal.minimal_of_privateRows
        intro c hcC
        refine ⟨{a, b, c}, ?_, hcC, by simp, ?_⟩
        · rw [hT]
          exact Finset.mem_insert_of_mem (mem_threeStarRows.mpr ⟨c, hcC, rfl⟩)
        · intro y hyC hyRow
          simp only [Finset.mem_insert, Finset.mem_singleton] at hyRow
          rcases hyRow with hya | hyb | hyc
          · exact (haC (hya ▸ hyC)).elim
          · exact (hbC (hyb ▸ hyC)).elim
          · exact hyc
      exact ⟨C, hCBlocker, by omega⟩
    · have hDisjoint : Disjoint Q C := Finset.disjoint_left.mpr (by
        intro q hqQ hqC
        exact hMeet ⟨q, Finset.mem_inter.mpr ⟨hqQ, hqC⟩⟩)
      obtain ⟨q, hqQ⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
      let S := insert q C
      have hqC : q ∉ C := fun hqC ↦ Finset.disjoint_left.mp hDisjoint hqQ hqC
      have hSTransversal : IsTransversal T S := by
        intro E hET
        rw [hT] at hET
        simp only [Finset.mem_insert] at hET
        rcases hET with rfl | hEStar
        · exact ⟨q, by simp [S], hqQ⟩
        · obtain ⟨c, hcC, rfl⟩ := mem_threeStarRows.mp hEStar
          exact ⟨c, by simp [S, hcC], by simp⟩
      have hSBlocker : S ∈ blocker T := by
        apply mem_blocker.mpr
        apply hSTransversal.minimal_of_privateRows
        intro z hzS
        simp only [S, Finset.mem_insert] at hzS
        rcases hzS with rfl | hzC
        · refine ⟨Q, hQT, by simp [S], hqQ, ?_⟩
          intro y hyS hyQ
          simp only [S, Finset.mem_insert] at hyS
          rcases hyS with hyq | hyC
          · exact hyq
          · exact (Finset.disjoint_left.mp hDisjoint hyQ hyC).elim
        · refine ⟨{a, b, z}, ?_, by simp [S, hzC], by simp, ?_⟩
          · rw [hT]
            exact Finset.mem_insert_of_mem (mem_threeStarRows.mpr ⟨z, hzC, rfl⟩)
          · intro y hyS hyRow
            simp only [S, Finset.mem_insert] at hyS
            simp only [Finset.mem_insert, Finset.mem_singleton] at hyRow
            rcases hyS with hyq | hyC
            · subst y
              rcases hyRow with hqa | hqb | hqz
              · exact (haQ (hqa ▸ hqQ)).elim
              · exact (hbQ (hqb ▸ hqQ)).elim
              · exact (hqC (hqz.symm ▸ hzC)).elim
            · rcases hyRow with hya | hyb | hyz
              · exact (haC (hya ▸ hyC)).elim
              · exact (hbC (hyb ▸ hyC)).elim
              · exact hyz
      have hSCard : S.card = 4 := by simp [S, hqC, hC]
      exact ⟨S, hSBlocker, by omega⟩
  obtain ⟨S, hSBlocker, hSCard⟩ := hExtra
  have hSNotPairs : S ∉ pairs := by
    intro hSPairs
    obtain ⟨s, hs, q, hqQ, hsqS⟩ := mem_crossPairRows.mp hSPairs
    have hsq : s ≠ q := by
      intro hsq
      subst q
      exact Finset.disjoint_left.mp hPairDisjoint hs hqQ
    have hPairCard : ({s, q} : Row α).card = 2 := by simp [hsq]
    rw [hsqS] at hPairCard
    exact hSCard hPairCard
  have hInsertSubset : insert S pairs ⊆ blocker T := by
    intro E hE
    simp only [Finset.mem_insert] at hE
    rcases hE with rfl | hEPairs
    · exact hSBlocker
    · exact hPairSubset hEPairs
  calc
    7 ≤ pairs.card + 1 := by omega
    _ = (insert S pairs).card := (Finset.card_insert_of_notMem hSNotPairs).symm
    _ ≤ (blocker T).card := Finset.card_le_card hInsertSubset

end AiMathLab.P0054.G419
