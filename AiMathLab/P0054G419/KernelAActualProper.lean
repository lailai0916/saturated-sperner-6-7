import AiMathLab.P0054G419.KernelAActualRows

namespace AiMathLab.P0054.G419

open G413

theorem fourRows_exists_missing_row {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2) (x : α) :
    ∃ row : FourVertex, x ∉ (rowOrder row : Row α) := by
  by_contra hMissing
  push_neg at hMissing
  have hSingletonTransversal : IsTransversal T {x} := by
    intro E hET
    let e : T := ⟨E, hET⟩
    obtain ⟨row, hrow⟩ := rowOrder.surjective e
    refine ⟨x, by simp, ?_⟩
    simpa [e, hrow] using hMissing row
  have hSingletonMinimal : IsMinimalTransversal T {x} := by
    refine isMinimalTransversal_iff.mpr ⟨hSingletonTransversal, ?_⟩
    intro S hS hTransversal
    have hSEmpty : S = ∅ := Finset.eq_empty_of_ssubset_singleton hS
    subst S
    obtain ⟨y, hyEmpty, -⟩ :=
      hTransversal (rowOrder 0 : Row α) (rowOrder 0).property
    simp at hyEmpty
  have hSingletonBlocker : ({x} : Row α) ∈ blocker T :=
    mem_blocker.mpr hSingletonMinimal
  have hLarge := hBRows {x} hSingletonBlocker
  simp at hLarge

theorem fourRows_actual_support_proper {α : Type*}
    [Fintype α] [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2) :
    ∀ x ∈ fourActiveUniverse T,
      ∃ row : FourVertex, x ∉ (rowOrder row : Row α) := by
  intro x _hx
  exact fourRows_exists_missing_row rowOrder hBRows x

end AiMathLab.P0054.G419
