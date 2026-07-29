import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Minimal

namespace AiMathLab.P0054.G413

abbrev Row (α : Type*) := Finset α

abbrev Hypergraph (α : Type*) := Finset (Row α)

def IsTransversal {α : Type*} (H : Hypergraph α) (T : Row α) : Prop :=
  ∀ E ∈ H, ∃ x ∈ T, x ∈ E

def IsMinimalTransversal {α : Type*} (H : Hypergraph α) (T : Row α) : Prop :=
  Minimal (IsTransversal H) T

def IsClutter {α : Type*} (H : Hypergraph α) : Prop :=
  ∀ ⦃A⦄, A ∈ H → ∀ ⦃B⦄, B ∈ H → A ⊆ B → A = B

def RowsNonempty {α : Type*} (H : Hypergraph α) : Prop :=
  ∀ E ∈ H, E.Nonempty

def RowsCardAtLeast {α : Type*} (H : Hypergraph α) (n : Nat) : Prop :=
  ∀ E ∈ H, n ≤ E.card

noncomputable def blocker {α : Type*} [Fintype α] (H : Hypergraph α) : Hypergraph α := by
  classical
  exact Finset.univ.powerset.filter (IsMinimalTransversal H)

def degree {α : Type*} [DecidableEq α] (H : Hypergraph α) (x : α) : Nat :=
  (H.filter fun E ↦ x ∈ E).card

def MaxDegreeAtMost {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (d : Nat) : Prop :=
  ∀ x, degree H x ≤ d

def pairRows {α : Type*} (H : Hypergraph α) : Hypergraph α :=
  H.filter fun E ↦ E.card = 2

def deletePoint {α : Type*} [DecidableEq α] (H : Hypergraph α) (x : α) : Hypergraph α :=
  H.image fun E ↦ E.erase x

noncomputable def minimize {α : Type*} (H : Hypergraph α) : Hypergraph α := by
  classical
  exact H.filter fun E ↦ ∀ F ∈ H, F ⊆ E → E ⊆ F

def IsPrivateRowFor {α : Type*} (H : Hypergraph α) (T : Row α) (x : α)
    (E : Row α) : Prop :=
  E ∈ H ∧ x ∈ T ∧ x ∈ E ∧ ∀ ⦃y⦄, y ∈ T → y ∈ E → y = x

theorem degree_mono {α : Type*} [DecidableEq α] {H K : Hypergraph α}
    (hHK : H ⊆ K) (x : α) : degree H x ≤ degree K x := by
  apply Finset.card_le_card
  intro E hE
  obtain ⟨hEH, hxE⟩ := Finset.mem_filter.mp hE
  exact Finset.mem_filter.mpr ⟨hHK hEH, hxE⟩

theorem degree_insert_of_notMem {α : Type*} [DecidableEq α]
    {H : Hypergraph α} {E : Row α} (hEH : E ∉ H) {x : α} (hxE : x ∈ E) :
    degree (insert E H) x = degree H x + 1 := by
  have hfilter :
      (insert E H).filter (fun A ↦ x ∈ A) = insert E (H.filter fun A ↦ x ∈ A) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hAH, hxA⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hAH, hxA⟩
    · rintro (rfl | ⟨hAH, hxA⟩)
      · exact ⟨Or.inl rfl, hxE⟩
      · exact ⟨Or.inr hAH, hxA⟩
  have hEnot : E ∉ H.filter (fun A ↦ x ∈ A) :=
    fun h ↦ hEH (Finset.mem_filter.mp h).1
  rw [degree, hfilter, Finset.card_insert_of_notMem hEnot]
  rfl

@[simp]
theorem mem_blocker {α : Type*} [Fintype α] {H : Hypergraph α} {T : Row α} :
    T ∈ blocker H ↔ IsMinimalTransversal H T := by
  classical
  simp [blocker]

theorem IsMinimalTransversal.transversal {α : Type*} {H : Hypergraph α} {T : Row α}
    (hT : IsMinimalTransversal H T) : IsTransversal H T :=
  hT.prop

theorem IsTransversal.mono {α : Type*} {H : Hypergraph α} {S T : Row α}
    (hS : IsTransversal H S) (hST : S ⊆ T) : IsTransversal H T := by
  intro E hE
  obtain ⟨x, hxS, hxE⟩ := hS E hE
  exact ⟨x, hST hxS, hxE⟩

theorem isMinimalTransversal_iff {α : Type*} {H : Hypergraph α} {T : Row α} :
    IsMinimalTransversal H T ↔
      IsTransversal H T ∧ ∀ ⦃S⦄, S ⊂ T → ¬ IsTransversal H S := by
  exact minimal_iff_forall_lt

theorem exists_minimalTransversal_subset {α : Type*} {H : Hypergraph α} {T : Row α}
    (hT : IsTransversal H T) :
    ∃ S, S ⊆ T ∧ IsMinimalTransversal H S := by
  obtain ⟨S, hST, hS⟩ := exists_minimal_le_of_wellFoundedLT (IsTransversal H) T hT
  exact ⟨S, hST, hS⟩

theorem univ_transversal {α : Type*} [Fintype α] {H : Hypergraph α}
    (hH : RowsNonempty H) : IsTransversal H Finset.univ := by
  intro E hE
  obtain ⟨x, hxE⟩ := hH E hE
  exact ⟨x, Finset.mem_univ x, hxE⟩

theorem blocker_nonempty {α : Type*} [Fintype α] {H : Hypergraph α}
    (hH : RowsNonempty H) : (blocker H).Nonempty := by
  classical
  obtain ⟨T, -, hT⟩ := exists_minimalTransversal_subset (univ_transversal hH)
  exact ⟨T, mem_blocker.mpr hT⟩

theorem blocker_isClutter {α : Type*} [Fintype α] (H : Hypergraph α) :
    IsClutter (blocker H) := by
  classical
  intro A hA B hB hAB
  have hAmin := mem_blocker.mp hA
  have hBmin := mem_blocker.mp hB
  exact Finset.Subset.antisymm hAB (hBmin.le_of_le hAmin.prop hAB)

theorem row_transversal_blocker {α : Type*} [Fintype α] {H : Hypergraph α}
    {E : Row α} (hE : E ∈ H) : IsTransversal (blocker H) E := by
  classical
  intro T hT
  obtain ⟨x, hxT, hxE⟩ := (mem_blocker.mp hT).prop E hE
  exact ⟨x, hxE, hxT⟩

theorem contains_row_of_transversal_blocker {α : Type*} [Fintype α]
    {H : Hypergraph α} {T : Row α} (hT : IsTransversal (blocker H) T) :
    ∃ E ∈ H, E ⊆ T := by
  classical
  by_contra h
  push Not at h
  have hcompl : IsTransversal H (Finset.univ \ T) := by
    intro E hE
    have hnot : ¬ E ⊆ T := h E hE
    obtain ⟨x, hxE, hxT⟩ := Finset.not_subset.mp hnot
    exact ⟨x, by simp [hxT], hxE⟩
  obtain ⟨S, hScompl, hSmin⟩ := exists_minimalTransversal_subset hcompl
  have hSb : S ∈ blocker H := mem_blocker.mpr hSmin
  obtain ⟨x, hxT, hxS⟩ := hT S hSb
  have hxnot : x ∉ T := by simpa using (hScompl hxS)
  exact hxnot hxT

theorem row_minimalTransversal_blocker {α : Type*} [Fintype α]
    {H : Hypergraph α} (hH : IsClutter H) {E : Row α} (hE : E ∈ H) :
    IsMinimalTransversal (blocker H) E := by
  classical
  refine ⟨row_transversal_blocker hE, ?_⟩
  intro T hT hTE
  obtain ⟨A, hAH, hAT⟩ := contains_row_of_transversal_blocker hT
  have hAE : A ⊆ E := hAT.trans hTE
  have hEq : A = E := hH hAH hE hAE
  simpa [hEq] using hAT

theorem blocker_involution {α : Type*} [Fintype α] {H : Hypergraph α}
    (hH : IsClutter H) : blocker (blocker H) = H := by
  classical
  ext T
  constructor
  · intro hT
    have hTmin : IsMinimalTransversal (blocker H) T := mem_blocker.mp hT
    obtain ⟨E, hEH, hET⟩ := contains_row_of_transversal_blocker hTmin.prop
    have hEtrans : IsTransversal (blocker H) E := row_transversal_blocker hEH
    have hTE : T ⊆ E := hTmin.le_of_le hEtrans hET
    have hEq : T = E := Finset.Subset.antisymm hTE hET
    simpa [hEq] using hEH
  · intro hT
    exact mem_blocker.mpr (row_minimalTransversal_blocker hH hT)

end AiMathLab.P0054.G413
