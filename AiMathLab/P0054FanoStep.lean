import AiMathLab.P0054MiddleSevenEightFiniteCore

namespace AiMathLab.P0054.FanoStep

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420

theorem fastBlockerExpand_mem_iff {α : Type*} [DecidableEq α]
    {base : G413.Hypergraph α} {R A : Row α} :
    A ∈ fastBlockerExpand base R ↔
      (∃ L ∈ base, ¬Disjoint L R ∧ A = L) ∨
        (∃ L ∈ base, Disjoint L R ∧ ∃ r ∈ R, A = insert r L) := by
  unfold fastBlockerExpand
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨L, hL, hA⟩
    by_cases hDisjoint : Disjoint L R
    · right
      rw [if_pos hDisjoint] at hA
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hA
      exact ⟨L, hL, hDisjoint, r, hr, rfl⟩
    · left
      rw [if_neg hDisjoint] at hA
      exact ⟨L, hL, hDisjoint, by simpa using hA⟩
  · rintro (⟨L, hL, hNotDisjoint, hEq⟩ |
      ⟨L, hL, hDisjoint, r, hr, hEq⟩)
    · subst A
      exact ⟨L, hL, by simp [hNotDisjoint]⟩
    · subst A
      refine ⟨L, hL, ?_⟩
      rw [if_pos hDisjoint]
      exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

theorem fastMinimize_eq_self_of_clutter {α : Type*} [DecidableEq α]
    {rows : G413.Hypergraph α} (hRows : IsClutter rows) :
    fastMinimize rows = rows := by
  ext row
  simp only [mem_fastMinimize]
  constructor
  · exact fun h ↦ h.1
  · intro hRow
    refine ⟨hRow, ?_⟩
    intro other hOther hSubset
    exact (hRows hOther hRow hSubset).symm.subset

theorem old_line_not_subset_extension {α : Type*} [DecidableEq α]
    {base : G413.Hypergraph α} {R M L : Row α} {r : α}
    (hRows : ∀ E ∈ base, E.card = 3)
    (hPairs : ∀ E ∈ base, ∀ F ∈ base, E ≠ F → (E ∩ F).card = 1)
    (hM : M ∈ base) (hL : L ∈ base)
    (hMNeL : M ≠ L) (hDisjoint : Disjoint L R) (hr : r ∈ R) :
    ¬M ⊆ insert r L := by
  intro hSubset
  have hrL : r ∉ L := fun hrL ↦ Finset.disjoint_left.mp hDisjoint hrL hr
  have hDiffSubset : M \ L ⊆ ({r} : Finset α) := by
    intro x hx
    have hxM := (Finset.mem_sdiff.mp hx).1
    have hxNotL := (Finset.mem_sdiff.mp hx).2
    have hxInsert := hSubset hxM
    simpa [hxNotL] using hxInsert
  have hInter : (L ∩ M).card = 1 := hPairs L hL M hM hMNeL.symm
  have hDiffCard : (M \ L).card = 2 := by
    rw [Finset.card_sdiff]
    rw [hRows M hM, hInter]
  have hCardLe := Finset.card_le_card hDiffSubset
  simp [hDiffCard] at hCardLe

theorem fastBlockerExpand_isClutter {α : Type*} [DecidableEq α]
    {base : G413.Hypergraph α} {R : Row α}
    (hRows : ∀ E ∈ base, E.card = 3)
    (hPairs : ∀ E ∈ base, ∀ F ∈ base, E ≠ F → (E ∩ F).card = 1) :
    IsClutter (fastBlockerExpand base R) := by
  intro A hA B hB hAB
  rw [fastBlockerExpand_mem_iff] at hA hB
  rcases hA with ⟨M, hM, hMMeet, hAM⟩ |
      ⟨M, hM, hMDisjoint, r, hr, hAM⟩
  · subst A
    rcases hB with ⟨L, hL, hLMeet, hBL⟩ |
        ⟨L, hL, hLDisjoint, s, hs, hBL⟩
    · subst B
      apply Finset.eq_of_subset_of_card_le hAB
      rw [hRows M hM, hRows L hL]
    · subst B
      by_cases hEq : M = L
      · subst L
        exact (hMMeet hLDisjoint).elim
      · exact (old_line_not_subset_extension hRows hPairs hM hL hEq
          hLDisjoint hs hAB).elim
  · subst A
    rcases hB with ⟨L, hL, hLMeet, hBL⟩ |
        ⟨L, hL, hLDisjoint, s, hs, hBL⟩
    · subst B
      have hrM : r ∉ M := fun hrM ↦
        Finset.disjoint_left.mp hMDisjoint hrM hr
      have hCardA : (insert r M).card = 4 := by
        rw [Finset.card_insert_of_notMem hrM, hRows M hM]
      have hCardB : L.card = 3 := hRows L hL
      have := Finset.card_le_card hAB
      omega
    · subst B
      apply Finset.eq_of_subset_of_card_le hAB
      have hrM : r ∉ M := fun hrM ↦
        Finset.disjoint_left.mp hMDisjoint hrM hr
      have hsL : s ∉ L := fun hsL ↦
        Finset.disjoint_left.mp hLDisjoint hsL hs
      rw [Finset.card_insert_of_notMem hrM,
        Finset.card_insert_of_notMem hsL, hRows M hM, hRows L hL]

theorem seven_lt_fastBlockerStep {α : Type*} [DecidableEq α]
    {base : G413.Hypergraph α} {R : Row α}
    (hBaseCard : base.card = 7)
    (hRows : ∀ E ∈ base, E.card = 3)
    (hPairs : ∀ E ∈ base, ∀ F ∈ base, E ≠ F → (E ∩ F).card = 1)
    (hRCard : 3 ≤ R.card)
    (hDisjoint : ∃ L ∈ base, Disjoint L R) :
    7 < (fastBlockerStep base R).card := by
  obtain ⟨L₀, hL₀, hL₀Disjoint⟩ := hDisjoint
  have hRTwo : 1 < R.card := by omega
  obtain ⟨r₀, hr₀, r₁, hr₁, hrNe⟩ := Finset.one_lt_card.mp hRTwo
  let f : Row α → Row α := fun L ↦
    if Disjoint L R then insert r₀ L else L
  have hfMem : ∀ L ∈ base, f L ∈ fastBlockerExpand base R := by
    intro L hL
    by_cases hLR : Disjoint L R
    · dsimp only [f]
      rw [if_pos hLR, fastBlockerExpand_mem_iff]
      exact Or.inr ⟨L, hL, hLR, r₀, hr₀, rfl⟩
    · dsimp only [f]
      rw [if_neg hLR, fastBlockerExpand_mem_iff]
      exact Or.inl ⟨L, hL, hLR, rfl⟩
  have hfInj : Set.InjOn f (↑base : Set (Row α)) := by
    intro L hL M hM hEq
    by_cases hLR : Disjoint L R <;> by_cases hMR : Disjoint M R
    · have hr₀L : r₀ ∉ L := fun hr₀L ↦
        Finset.disjoint_left.mp hLR hr₀L hr₀
      have hr₀M : r₀ ∉ M := fun hr₀M ↦
        Finset.disjoint_left.mp hMR hr₀M hr₀
      dsimp only [f] at hEq
      rw [if_pos hLR, if_pos hMR] at hEq
      have hErase := congrArg (Finset.erase · r₀) hEq
      simpa [hr₀L, hr₀M] using hErase
    · dsimp only [f] at hEq
      rw [if_pos hLR, if_neg hMR] at hEq
      have hr₀L : r₀ ∉ L := fun hr₀L ↦
        Finset.disjoint_left.mp hLR hr₀L hr₀
      have hCard := congrArg Finset.card hEq
      rw [Finset.card_insert_of_notMem hr₀L, hRows L hL, hRows M hM] at hCard
      omega
    · dsimp only [f] at hEq
      rw [if_neg hLR, if_pos hMR] at hEq
      have hr₀M : r₀ ∉ M := fun hr₀M ↦
        Finset.disjoint_left.mp hMR hr₀M hr₀
      have hCard := congrArg Finset.card hEq
      rw [Finset.card_insert_of_notMem hr₀M, hRows L hL, hRows M hM] at hCard
      omega
    · dsimp only [f] at hEq
      simpa [hLR, hMR] using hEq
  let q : Row α := insert r₁ L₀
  have hqMem : q ∈ fastBlockerExpand base R := by
    rw [fastBlockerExpand_mem_iff]
    exact Or.inr ⟨L₀, hL₀, hL₀Disjoint, r₁, hr₁, rfl⟩
  have hqNotImage : q ∉ base.image f := by
    intro hq
    obtain ⟨M, hM, hEq⟩ := Finset.mem_image.mp hq
    by_cases hMR : Disjoint M R
    · have hr₀M : r₀ ∉ M := fun hr₀M ↦
        Finset.disjoint_left.mp hMR hr₀M hr₀
      dsimp only [f, q] at hEq
      rw [if_pos hMR] at hEq
      have hr₁L₀ : r₁ ∉ L₀ := fun hr₁L₀ ↦
        Finset.disjoint_left.mp hL₀Disjoint hr₁L₀ hr₁
      have hr₁Right : r₁ ∈ insert r₀ M := by
        rw [hEq]
        simp
      have hr₁M : r₁ ∈ M := by
        simpa [hrNe.symm] using hr₁Right
      exact (Finset.disjoint_left.mp hMR hr₁M hr₁)
    · have hr₁L₀ : r₁ ∉ L₀ := fun hr₁L₀ ↦
        Finset.disjoint_left.mp hL₀Disjoint hr₁L₀ hr₁
      dsimp only [f, q] at hEq
      rw [if_neg hMR] at hEq
      have hCard := congrArg Finset.card hEq
      rw [hRows M hM, Finset.card_insert_of_notMem hr₁L₀,
        hRows L₀ hL₀] at hCard
      omega
  have hLargeSubset : insert q (base.image f) ⊆
      fastBlockerExpand base R := by
    intro A hA
    simp only [Finset.mem_insert] at hA
    rcases hA with rfl | hA
    · exact hqMem
    · obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hA
      exact hfMem L hL
  have hExpansionCard : 8 ≤ (fastBlockerExpand base R).card := by
    calc
      8 = (insert q (base.image f)).card := by
        rw [Finset.card_insert_of_notMem hqNotImage,
          Finset.card_image_of_injOn hfInj, hBaseCard]
      _ ≤ (fastBlockerExpand base R).card :=
        Finset.card_le_card hLargeSubset
  unfold fastBlockerStep
  rw [fastMinimize_eq_self_of_clutter
    (fastBlockerExpand_isClutter hRows hPairs)]
  omega

end AiMathLab.P0054.FanoStep
