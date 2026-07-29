import AiMathLab.P0054G413.BlockerInvolution

namespace AiMathLab.P0054.G413

def avoidPoint {α : Type*} [DecidableEq α] (H : Hypergraph α) (x : α) : Hypergraph α :=
  H.filter fun E ↦ x ∉ E

noncomputable def residual {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (x : α) : Hypergraph α :=
  minimize (deletePoint H x)

@[simp]
theorem mem_minimize {α : Type*} {H : Hypergraph α} {E : Row α} :
    E ∈ minimize H ↔ E ∈ H ∧ ∀ F ∈ H, F ⊆ E → E ⊆ F := by
  classical
  simp [minimize]

@[simp]
theorem mem_avoidPoint {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {E : Row α} :
    E ∈ avoidPoint H x ↔ E ∈ H ∧ x ∉ E := by
  classical
  simp [avoidPoint]

theorem minimize_subset {α : Type*} (H : Hypergraph α) : minimize H ⊆ H := by
  classical
  intro E hE
  exact (mem_minimize.mp hE).1

theorem minimize_isClutter {α : Type*} (H : Hypergraph α) : IsClutter (minimize H) := by
  classical
  intro A hA B hB hAB
  exact Finset.Subset.antisymm hAB ((mem_minimize.mp hB).2 A (mem_minimize.mp hA).1 hAB)

theorem exists_minimize_subset {α : Type*} {H : Hypergraph α} {E : Row α}
    (hE : E ∈ H) : ∃ M ∈ minimize H, M ⊆ E := by
  classical
  obtain ⟨M, hME, hMmin⟩ := exists_minimal_le_of_wellFoundedLT (fun A ↦ A ∈ H) E hE
  refine ⟨M, mem_minimize.mpr ⟨hMmin.prop, ?_⟩, hME⟩
  intro A hAH hAM
  exact hMmin.le_of_le hAH hAM

theorem transversal_minimize_iff {α : Type*} {H : Hypergraph α} {T : Row α} :
    IsTransversal (minimize H) T ↔ IsTransversal H T := by
  classical
  constructor
  · intro hT E hE
    obtain ⟨M, hMmin, hME⟩ := exists_minimize_subset hE
    obtain ⟨x, hxT, hxM⟩ := hT M hMmin
    exact ⟨x, hxT, hME hxM⟩
  · intro hT E hE
    exact hT E (minimize_subset H hE)

theorem minimalTransversal_minimize_iff {α : Type*} {H : Hypergraph α} {T : Row α} :
    IsMinimalTransversal (minimize H) T ↔ IsMinimalTransversal H T := by
  simp only [isMinimalTransversal_iff, transversal_minimize_iff]

theorem blocker_minimize {α : Type*} [Fintype α] (H : Hypergraph α) :
    blocker (minimize H) = blocker H := by
  classical
  ext T
  simp [minimalTransversal_minimize_iff]

theorem deletePoint_rows_avoid {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {E : Row α} (hE : E ∈ deletePoint H x) : x ∉ E := by
  rcases Finset.mem_image.mp hE with ⟨A, -, rfl⟩
  simp

theorem transversal_deletePoint_iff {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {T : Row α} (hxT : x ∉ T) :
    IsTransversal (deletePoint H x) T ↔ IsTransversal H T := by
  constructor
  · intro hT E hE
    have hErase : E.erase x ∈ deletePoint H x := Finset.mem_image.mpr ⟨E, hE, rfl⟩
    obtain ⟨y, hyT, hyE⟩ := hT (E.erase x) hErase
    exact ⟨y, hyT, Finset.mem_of_mem_erase hyE⟩
  · intro hT E hE
    rcases Finset.mem_image.mp hE with ⟨A, hAH, rfl⟩
    obtain ⟨y, hyT, hyA⟩ := hT A hAH
    have hyx : y ≠ x := fun hyx ↦ hxT (hyx ▸ hyT)
    exact ⟨y, hyT, Finset.mem_erase.mpr ⟨hyx, hyA⟩⟩

theorem minimalTransversal_deletePoint_avoids {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {T : Row α}
    (hT : IsMinimalTransversal (deletePoint H x) T) : x ∉ T := by
  intro hxT
  have herase : IsTransversal (deletePoint H x) (T.erase x) := by
    intro E hE
    obtain ⟨y, hyT, hyE⟩ := hT.prop E hE
    have hyx : y ≠ x := fun hyx ↦ deletePoint_rows_avoid hE (hyx ▸ hyE)
    exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hyT⟩, hyE⟩
  have hsubset : T.erase x ⊆ T := Finset.erase_subset x T
  have hreverse : T ⊆ T.erase x := hT.le_of_le herase hsubset
  have hxErase : x ∈ T.erase x := hreverse hxT
  simp at hxErase

theorem minimalTransversal_deletePoint_iff {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {x : α} {T : Row α} (hxT : x ∉ T) :
    IsMinimalTransversal (deletePoint H x) T ↔ IsMinimalTransversal H T := by
  constructor
  · intro hT
    refine isMinimalTransversal_iff.mpr ⟨(transversal_deletePoint_iff hxT).mp hT.prop, ?_⟩
    intro S hST hS
    have hxS : x ∉ S := fun hx ↦ hxT (hST.le hx)
    exact (isMinimalTransversal_iff.mp hT).2 hST ((transversal_deletePoint_iff hxS).mpr hS)
  · intro hT
    refine isMinimalTransversal_iff.mpr ⟨(transversal_deletePoint_iff hxT).mpr hT.prop, ?_⟩
    intro S hST hS
    have hxS : x ∉ S := fun hx ↦ hxT (hST.le hx)
    exact (isMinimalTransversal_iff.mp hT).2 hST ((transversal_deletePoint_iff hxS).mp hS)

theorem blocker_deletePoint {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (x : α) :
    blocker (deletePoint H x) = avoidPoint (blocker H) x := by
  classical
  ext T
  constructor
  · intro hT
    have hTmin := mem_blocker.mp hT
    have hxT := minimalTransversal_deletePoint_avoids hTmin
    exact mem_avoidPoint.mpr
      ⟨mem_blocker.mpr ((minimalTransversal_deletePoint_iff hxT).mp hTmin), hxT⟩
  · intro hT
    obtain ⟨hTb, hxT⟩ := mem_avoidPoint.mp hT
    exact mem_blocker.mpr ((minimalTransversal_deletePoint_iff hxT).mpr (mem_blocker.mp hTb))

theorem blocker_residual {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (x : α) :
    blocker (residual H x) = avoidPoint (blocker H) x := by
  classical
  rw [residual, blocker_minimize, blocker_deletePoint]

theorem residual_isClutter {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (x : α) : IsClutter (residual H x) := by
  classical
  exact minimize_isClutter _

theorem blocker_avoidPoint {α : Type*} [Fintype α] [DecidableEq α]
    {H : Hypergraph α} (hH : IsClutter H) (x : α) :
    blocker (avoidPoint H x) = residual (blocker H) x := by
  classical
  have hdual := blocker_residual (blocker H) x
  rw [blocker_involution hH] at hdual
  calc
    blocker (avoidPoint H x) = blocker (blocker (residual (blocker H) x)) := by rw [hdual]
    _ = residual (blocker H) x := blocker_involution (residual_isClutter _ _)

theorem card_avoidPoint_add_degree {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (x : α) :
    (avoidPoint H x).card + degree H x = H.card := by
  classical
  simpa [avoidPoint, degree] using
    (Finset.card_filter_add_card_filter_not (s := H) fun E ↦ x ∉ E)

theorem residual_card_le {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (x : α) : (residual H x).card ≤ H.card := by
  classical
  calc
    (residual H x).card ≤ (deletePoint H x).card :=
      Finset.card_le_card (minimize_subset _)
    _ ≤ H.card := Finset.card_image_le

theorem residual_rows_cardAtLeast {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {n : Nat} (hH : RowsCardAtLeast H n) (x : α) :
    RowsCardAtLeast (residual H x) (n - 1) := by
  classical
  intro E hE
  have hEdelete : E ∈ deletePoint H x := minimize_subset _ hE
  rcases Finset.mem_image.mp hEdelete with ⟨A, hAH, rfl⟩
  by_cases hxA : x ∈ A
  · rw [Finset.card_erase_of_mem hxA]
    exact Nat.sub_le_sub_right (hH A hAH) 1
  · rw [Finset.erase_eq_of_notMem hxA]
    exact (Nat.sub_le n 1).trans (hH A hAH)

theorem pairRows_residual_card_le_degree {α : Type*} [DecidableEq α]
    {H : Hypergraph α} (hH : RowsCardAtLeast H 3) (x : α) :
    (pairRows (residual H x)).card ≤ degree H x := by
  classical
  have exists_source {E : Row α} (hE : E ∈ pairRows (residual H x)) :
      ∃ A ∈ H, A.erase x = E := by
    have hEr : E ∈ residual H x := (Finset.mem_filter.mp hE).1
    have hEd : E ∈ deletePoint H x := minimize_subset _ hEr
    simpa [deletePoint] using hEd
  let source : Row α → Row α := fun E ↦
    if hE : E ∈ pairRows (residual H x) then Classical.choose (exists_source hE) else ∅
  have source_spec {E : Row α} (hE : E ∈ pairRows (residual H x)) :
      source E ∈ H ∧ (source E).erase x = E := by
    simp only [source, dif_pos hE]
    exact Classical.choose_spec (exists_source hE)
  have source_contains {E : Row α} (hE : E ∈ pairRows (residual H x)) :
      x ∈ source E := by
    by_contra hx
    have hcardSource : 3 ≤ (source E).card := hH _ (source_spec hE).1
    have hcardE : E.card = 2 := (Finset.mem_filter.mp hE).2
    have hEq : source E = E := by
      calc
        source E = (source E).erase x := (Finset.erase_eq_of_notMem hx).symm
        _ = E := (source_spec hE).2
    have hcardEq := congrArg Finset.card hEq
    omega
  apply Finset.card_le_card_of_injOn source
  · intro E hE
    exact Finset.mem_filter.mpr ⟨(source_spec hE).1, source_contains hE⟩
  · intro E hE F hF hEq
    calc
      E = (source E).erase x := (source_spec hE).2.symm
      _ = (source F).erase x := by rw [hEq]
      _ = F := (source_spec hF).2

end AiMathLab.P0054.G413
