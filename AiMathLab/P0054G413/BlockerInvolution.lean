import AiMathLab.P0054G413.ClutterBasic

namespace AiMathLab.P0054.G413

theorem IsMinimalTransversal.exists_privateRow {α : Type*} {H : Hypergraph α}
    {T : Row α} (hT : IsMinimalTransversal H T) {x : α} (hxT : x ∈ T) :
    ∃ E, IsPrivateRowFor H T x E := by
  classical
  by_contra h
  push Not at h
  have herase : IsTransversal H (T.erase x) := by
    intro E hE
    obtain ⟨y, hyT, hyE⟩ := hT.prop E hE
    by_cases hyx : y = x
    · subst y
      have hnotPrivate := h E
      simp only [IsPrivateRowFor, hE, hxT, hyE, true_and] at hnotPrivate
      push Not at hnotPrivate
      obtain ⟨z, hzT, hzE, hzx⟩ := hnotPrivate
      exact ⟨z, Finset.mem_erase.mpr ⟨hzx, hzT⟩, hzE⟩
    · exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hyT⟩, hyE⟩
  have hsubset : T.erase x ⊆ T := Finset.erase_subset x T
  have hreverse : T ⊆ T.erase x := hT.le_of_le herase hsubset
  have hxErase : x ∈ T.erase x := hreverse hxT
  simp at hxErase

theorem IsMinimalTransversal.avoids_inactive {α : Type*} {H : Hypergraph α}
    {T : Row α} (hT : IsMinimalTransversal H T) {x : α}
    (hxH : ∀ E ∈ H, x ∉ E) : x ∉ T := by
  classical
  intro hxT
  have herase : IsTransversal H (T.erase x) := by
    intro E hE
    obtain ⟨y, hyT, hyE⟩ := hT.prop E hE
    have hyx : y ≠ x := fun hyx ↦ hxH E hE (hyx ▸ hyE)
    exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hyT⟩, hyE⟩
  have hsubset : T.erase x ⊆ T := Finset.erase_subset x T
  have hreverse : T ⊆ T.erase x := hT.le_of_le herase hsubset
  have hxErase : x ∈ T.erase x := hreverse hxT
  simp at hxErase

theorem blocker_rows_avoid_inactive {α : Type*} [Fintype α]
    {H : Hypergraph α} {x : α} (hxH : ∀ E ∈ H, x ∉ E) :
    ∀ T ∈ blocker H, x ∉ T := by
  classical
  intro T hT
  exact (mem_blocker.mp hT).avoids_inactive hxH

theorem minimalTransversal_card_le_rows {α : Type*} {H : Hypergraph α}
    {T : Row α} (hT : IsMinimalTransversal H T) : T.card ≤ H.card := by
  classical
  let witness : α → Row α := fun x ↦
    if hx : x ∈ T then Classical.choose (hT.exists_privateRow hx) else ∅
  have hwitness {x : α} (hx : x ∈ T) : IsPrivateRowFor H T x (witness x) := by
    simp only [witness, dif_pos hx]
    exact Classical.choose_spec (hT.exists_privateRow hx)
  apply Finset.card_le_card_of_injOn witness
  · intro x hx
    exact (hwitness hx).1
  · intro x hx y hy hxy
    have hxPrivate := hwitness hx
    have hyPrivate := hwitness hy
    have hyIn : y ∈ witness x := by simpa [hxy] using hyPrivate.2.2.1
    exact (hxPrivate.2.2.2 hy hyIn).symm

theorem exists_blocker_private_at_row {α : Type*} [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) {E : Row α} (hEH : E ∈ H)
    {x : α} (hxE : x ∈ E) :
    ∃ T ∈ blocker H, IsPrivateRowFor H T x E := by
  classical
  let C : Row α := insert x (Finset.univ \ E)
  have hC : IsTransversal H C := by
    intro A hAH
    by_cases hxA : x ∈ A
    · exact ⟨x, Finset.mem_insert_self x _, hxA⟩
    · have hnotSubset : ¬ A ⊆ E := by
        intro hAE
        have hEq : A = E := hH hAH hEH hAE
        exact hxA (hEq ▸ hxE)
      obtain ⟨y, hyA, hyE⟩ := Finset.not_subset.mp hnotSubset
      exact ⟨y, by simp [C, hyE], hyA⟩
  obtain ⟨T, hTC, hTmin⟩ := exists_minimalTransversal_subset hC
  have hTb : T ∈ blocker H := mem_blocker.mpr hTmin
  obtain ⟨y, hyT, hyE⟩ := hTmin.prop E hEH
  have hyC := hTC hyT
  have hyx : y = x := by
    simp only [C, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and] at hyC
    rcases hyC with hyx | hyNotE
    · exact hyx
    · exact (hyNotE hyE).elim
  subst y
  refine ⟨T, hTb, hEH, ?_, hxE, ?_⟩
  · exact hyT
  intro y hyT hyE
  have hyC := hTC hyT
  simp only [C, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and] at hyC
  rcases hyC with hyx | hyNotE
  · exact hyx
  · exact (hyNotE hyE).elim

theorem point_mem_some_blocker {α : Type*} [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) {E : Row α} (hEH : E ∈ H)
    {x : α} (hxE : x ∈ E) :
    ∃ T ∈ blocker H, x ∈ T := by
  obtain ⟨T, hTb, hPrivate⟩ := exists_blocker_private_at_row hH hEH hxE
  exact ⟨T, hTb, hPrivate.2.1⟩

end AiMathLab.P0054.G413
