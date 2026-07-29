import AiMathLab.P0054G419

namespace AiMathLab.P0054.G420

open G413

noncomputable def middleIndexSet {α : Type*} [Fintype α] [DecidableEq α]
    (H : G413.Hypergraph α) : Finset (Row α ⊕ Row α) :=
  H.disjSum (blocker H)

def middleEvent {α : Type*} [Fintype α] [DecidableEq α] :
    Row α ⊕ Row α → Finset (Row α)
  | Sum.inl D => Finset.Icc D Finset.univ
  | Sum.inr E => (Finset.univ \ E).powerset

theorem middleIndexSet_card {α : Type*} [Fintype α] [DecidableEq α]
    (H : G413.Hypergraph α) :
    (middleIndexSet H).card = H.card + (blocker H).card := by
  simp [middleIndexSet]

theorem middleEvent_subset_powerset {α : Type*}
    [Fintype α] [DecidableEq α] (i : Row α ⊕ Row α) :
    middleEvent i ⊆ Finset.univ.powerset := by
  intro R hR
  cases i with
  | inl D =>
      exact Finset.mem_powerset.mpr (Finset.mem_Icc.mp hR).2
  | inr E =>
      exact Finset.mem_powerset.mpr
        ((Finset.mem_powerset.mp hR).trans Finset.sdiff_subset)

theorem middleEvent_card_le {α : Type*}
    [Fintype α] [DecidableEq α]
    {i : Row α ⊕ Row α}
    (hRows : ∀ D : Row α, i = Sum.inl D → 4 ≤ D.card)
    (hBlockerRows : ∀ E : Row α, i = Sum.inr E → 4 ≤ E.card) :
    (middleEvent i).card ≤ 2 ^ (Fintype.card α - 4) := by
  cases i with
  | inl D =>
      rw [middleEvent, Finset.card_Icc_finset (Finset.subset_univ D)]
      apply Nat.pow_le_pow_right (by omega)
      have hD := hRows D rfl
      simpa using Nat.sub_le_sub_left hD (Fintype.card α)
  | inr E =>
      rw [middleEvent, Finset.card_powerset,
        Finset.card_sdiff_of_subset (Finset.subset_univ E)]
      apply Nat.pow_le_pow_right (by omega)
      have hE := hBlockerRows E rfl
      simpa using Nat.sub_le_sub_left hE (Fintype.card α)

theorem middleEvents_cover {α : Type*}
    [Fintype α] [DecidableEq α]
    (H : G413.Hypergraph α) :
    Finset.univ.powerset ⊆
      (middleIndexSet H).biUnion middleEvent := by
  classical
  intro R hR
  by_cases hContains : ∃ D ∈ H, D ⊆ R
  · obtain ⟨D, hDH, hDR⟩ := hContains
    apply Finset.mem_biUnion.mpr
    refine ⟨Sum.inl D, ?_, ?_⟩
    · simp [middleIndexSet, hDH]
    · exact Finset.mem_Icc.mpr ⟨hDR, Finset.subset_univ R⟩
  · push Not at hContains
    have hComplementTransversal : IsTransversal H (Finset.univ \ R) := by
      intro D hDH
      obtain ⟨x, hxD, hxR⟩ := Finset.not_subset.mp (hContains D hDH)
      exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxR⟩, hxD⟩
    obtain ⟨E, hEComplement, hEMinimal⟩ :=
      exists_minimalTransversal_subset hComplementTransversal
    have hEBlocker : E ∈ blocker H := mem_blocker.mpr hEMinimal
    apply Finset.mem_biUnion.mpr
    refine ⟨Sum.inr E, ?_, ?_⟩
    · simp [middleIndexSet, hEBlocker]
    · apply Finset.mem_powerset.mpr
      intro x hxR
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hxE ↦
        (Finset.mem_sdiff.mp (hEComplement hxE)).2 hxR⟩

theorem card_biUnion_lt_sum_of_overlap
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    {I : Finset ι} {events : ι → Finset β}
    {i j : ι} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j)
    (hoverlap : (events i ∩ events j).Nonempty) :
    (I.biUnion events).card < ∑ k ∈ I, (events k).card := by
  let rest := (I.erase i).erase j
  have hjErase : j ∈ I.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hI : I = insert i (insert j rest) := by
    ext k
    simp [rest]
    constructor
    · intro hk
      by_cases hki : k = i
      · exact Or.inl hki
      by_cases hkj : k = j
      · exact Or.inr (Or.inl hkj)
      · exact Or.inr (Or.inr ⟨hkj, hki, hk⟩)
    · rintro (rfl | rfl | ⟨hkj, hki, hk⟩)
      · exact hi
      · exact hj
      · exact hk
  have hiRest : i ∉ rest := by simp [rest, hij]
  have hjRest : j ∉ rest := by simp [rest]
  have hUnionStrict :
      (events i ∪ events j).card < (events i).card + (events j).card := by
    rw [← Finset.card_union_add_card_inter]
    exact Nat.lt_add_of_pos_right (Finset.card_pos.mpr hoverlap)
  have hiInsertRest : i ∉ insert j rest := by simp [hij, hiRest]
  have hUnionEq :
      I.biUnion events = (events i ∪ events j) ∪ rest.biUnion events := by
    rw [hI, Finset.biUnion_insert, Finset.biUnion_insert]
    simp only [Finset.union_assoc]
  have hSumEq :
      (∑ k ∈ I, (events k).card) =
        (events i).card + (events j).card +
          ∑ k ∈ rest, (events k).card := by
    rw [hI, Finset.sum_insert hiInsertRest, Finset.sum_insert hjRest]
    omega
  rw [hUnionEq, hSumEq]
  calc
    ((events i ∪ events j) ∪ rest.biUnion events).card ≤
        (events i ∪ events j).card + (rest.biUnion events).card :=
      Finset.card_union_le _ _
    _ < ((events i).card + (events j).card) +
        (rest.biUnion events).card := Nat.add_lt_add_right hUnionStrict _
    _ ≤ ((events i).card + (events j).card) +
        ∑ k ∈ rest, (events k).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _

theorem middle_has_three_row {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (_hHClutter : IsClutter H)
    (hTotal : H.card + (blocker H).card = 16)
    (hRows : RowsCardAtLeast H 3)
    (hBlockerRows : RowsCardAtLeast (blocker H) 3) :
    (∃ D ∈ H, D.card = 3) ∨
      ∃ E ∈ blocker H, E.card = 3 := by
  classical
  by_contra hNoThree
  push Not at hNoThree
  have hRowsFour : RowsCardAtLeast H 4 := by
    intro D hDH
    have := hRows D hDH
    have hne := hNoThree.1 D hDH
    omega
  have hBlockerRowsFour : RowsCardAtLeast (blocker H) 4 := by
    intro E hEH
    have := hBlockerRows E hEH
    have hne := hNoThree.2 E hEH
    omega
  have hHNonempty : H.Nonempty := by
    by_contra hEmpty
    have hHEmpty := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hEmptyBlocker : (∅ : Row α) ∈ blocker H := by
      rw [mem_blocker, isMinimalTransversal_iff, hHEmpty]
      simp [IsTransversal]
    have := hBlockerRowsFour ∅ hEmptyBlocker
    simp at this
  have hBNonempty : (blocker H).Nonempty := by
    exact blocker_nonempty (fun D hDH ↦
      Finset.card_pos.mp (by have := hRowsFour D hDH; omega))
  have hHCardTwo : 2 ≤ H.card := by
    by_contra hCard
    have hCardOne : H.card = 1 := by
      have := Finset.card_pos.mpr hHNonempty
      omega
    obtain ⟨D, hH⟩ := Finset.card_eq_one.mp hCardOne
    have hD : D ∈ H := by simp [hH]
    have hDNonempty : D.Nonempty :=
      Finset.card_pos.mp (by have := hRowsFour D hD; omega)
    obtain ⟨x, hxD⟩ := hDNonempty
    have hxBlocker : ({x} : Row α) ∈ blocker H := by
      rw [hH]
      exact (blocker_singletonFamily D).symm ▸ (by simp [hxD])
    have := hBlockerRowsFour {x} hxBlocker
    simp at this
  obtain ⟨D, E, hDH, hEH, hDE⟩ :=
    Finset.one_lt_card_iff.mp (by omega : 1 < H.card)
  let indices := middleIndexSet H
  have hIndexCard : indices.card = 16 := by
    simpa [indices, middleIndexSet] using hTotal
  have hEventBound :
      ∀ i ∈ indices, (middleEvent i).card ≤
        2 ^ (Fintype.card α - 4) := by
    intro i hi
    apply middleEvent_card_le
    · intro A hiA
      subst i
      exact hRowsFour A (by simpa [indices, middleIndexSet] using hi)
    · intro A hiA
      subst i
      exact hBlockerRowsFour A (by simpa [indices, middleIndexSet] using hi)
  have hGroundFour : 4 ≤ Fintype.card α := by
    have hDCard := hRowsFour D hDH
    exact hDCard.trans (Finset.card_le_univ D)
  have hPower :
      2 ^ Fintype.card α = 16 * 2 ^ (Fintype.card α - 4) := by
    calc
      2 ^ Fintype.card α = 2 ^ (4 + (Fintype.card α - 4)) := by
        rw [Nat.add_sub_of_le hGroundFour]
      _ = 16 * 2 ^ (Fintype.card α - 4) := by norm_num [pow_add]
  have hCoverCard :
      2 ^ Fintype.card α ≤ (indices.biUnion middleEvent).card := by
    calc
      2 ^ Fintype.card α = (Finset.univ.powerset : Finset (Row α)).card := by
        simp
      _ ≤ (indices.biUnion middleEvent).card :=
        Finset.card_le_card (by
          simpa [indices] using middleEvents_cover H)
  have hOverlap :
      (middleEvent (Sum.inl D) ∩ middleEvent (Sum.inl E)).Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp [middleEvent]
  have hStrict := card_biUnion_lt_sum_of_overlap
    (I := indices) (events := middleEvent)
    (i := Sum.inl D) (j := Sum.inl E)
    (by simp [indices, middleIndexSet, hDH])
    (by simp [indices, middleIndexSet, hEH])
    (by simpa using hDE) hOverlap
  have hSumUpper :
      (∑ i ∈ indices, (middleEvent i).card) ≤
        16 * 2 ^ (Fintype.card α - 4) := by
    calc
      (∑ i ∈ indices, (middleEvent i).card) ≤
          indices.card * 2 ^ (Fintype.card α - 4) :=
        Finset.sum_le_card_nsmul indices _ _ hEventBound
      _ = 16 * 2 ^ (Fintype.card α - 4) := by rw [hIndexCard]
  rw [← hPower] at hSumUpper
  omega

end AiMathLab.P0054.G420
