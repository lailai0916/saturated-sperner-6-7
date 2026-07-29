import Mathlib

/-!
# Generic saturated Sperner systems

This module contains only the symbolic definitions and elementary lemmas.  In
particular, no finiteness assumption is made on the ground type.
-/

universe u

namespace AiMathLab.SaturatedSperner

/-- A finite family of finite subsets of `α`. -/
abbrev Family (α : Type u) := Finset (Finset α)

variable {α : Type u} [DecidableEq α]

/-- A strict chain of length `d + 1` in `F` whose final member is `B`. -/
def HasStrictChainEndingAt : Nat → Family α → Finset α → Prop
  | 0, F, B => B ∈ F
  | d + 1, F, B =>
      B ∈ F ∧ ∃ A, HasStrictChainEndingAt d F A ∧ A ⊂ B

/-- `F` contains a strict-inclusion chain with exactly `r` members.
The empty chain witnesses `r = 0`. -/
def HasStrictChainLength : Nat → Family α → Prop
  | 0, _ => True
  | d + 1, F => ∃ B, HasStrictChainEndingAt d F B

/-- `F` has no strict chain of length `k + 1`. -/
def IsKSperner (k : Nat) (F : Family α) : Prop :=
  ¬ HasStrictChainLength (k + 1) F

/-- Standard saturation: `F` is `k`-Sperner, and adjoining every external
finite subset creates a forbidden chain. -/
def IsSaturatedKSperner (k : Nat) (F : Family α) : Prop :=
  IsKSperner k F ∧
    ∀ S : Finset α, S ∉ F →
      HasStrictChainLength (k + 1) (insert S F)

/-- A target-length chain exists after adjoining `S`, but not before. -/
def HasNewStrictChainAt (r : Nat) (F : Family α) (S : Finset α) : Prop :=
  HasStrictChainLength r (insert S F) ∧
    ¬ HasStrictChainLength r F

/-- The erase-critical predicate used by the legacy P0053 development.
It says that a target chain exists and erasing `S` destroys every such chain. -/
def HasEraseCriticalStrictChain
    (r : Nat) (G : Family α) (S : Finset α) : Prop :=
  HasStrictChainLength r G ∧
    ¬ HasStrictChainLength r (G.erase S)

@[simp] theorem hasStrictChainEndingAt_zero_iff
    (F : Family α) (B : Finset α) :
    HasStrictChainEndingAt 0 F B ↔ B ∈ F := by
  rfl

theorem hasStrictChainEndingAt_succ_iff
    (d : Nat) (F : Family α) (B : Finset α) :
    HasStrictChainEndingAt (d + 1) F B ↔
      B ∈ F ∧ ∃ A, HasStrictChainEndingAt d F A ∧ A ⊂ B := by
  rfl

@[simp] theorem hasStrictChainLength_zero (F : Family α) :
    HasStrictChainLength 0 F := by
  trivial

theorem hasStrictChainLength_succ_iff (d : Nat) (F : Family α) :
    HasStrictChainLength (d + 1) F ↔
      ∃ B, HasStrictChainEndingAt d F B := by
  rfl

theorem hasStrictChainEndingAt_mem
    {d : Nat} {F : Family α} {B : Finset α}
    (h : HasStrictChainEndingAt d F B) : B ∈ F := by
  cases d with
  | zero => exact h
  | succ d => exact h.1

theorem hasStrictChainEndingAt_extend
    {d : Nat} {F : Family α} {A B : Finset α}
    (hA : HasStrictChainEndingAt d F A)
    (hBF : B ∈ F) (hAB : A ⊂ B) :
    HasStrictChainEndingAt (d + 1) F B := by
  exact ⟨hBF, A, hA, hAB⟩

theorem strictSubset_trans {A B C : Finset α}
    (hAB : A ⊂ B) (hBC : B ⊂ C) : A ⊂ C :=
  lt_trans hAB hBC

theorem hasStrictChainEndingAt_mono_family
    {d : Nat} {F G : Family α} {B : Finset α}
    (hFG : F ⊆ G) (h : HasStrictChainEndingAt d F B) :
    HasStrictChainEndingAt d G B := by
  induction d generalizing B with
  | zero => exact hFG h
  | succ d ih =>
      rcases h with ⟨hBF, A, hA, hAB⟩
      exact ⟨hFG hBF, A, ih hA, hAB⟩

theorem hasStrictChainLength_mono_family
    {r : Nat} {F G : Family α}
    (hFG : F ⊆ G) (h : HasStrictChainLength r F) :
    HasStrictChainLength r G := by
  cases r with
  | zero => trivial
  | succ d =>
      rcases h with ⟨B, hB⟩
      exact ⟨B, hasStrictChainEndingAt_mono_family hFG hB⟩

theorem isKSperner_of_subset
    {k : Nat} {F G : Family α} (hFG : F ⊆ G)
    (hG : IsKSperner k G) : IsKSperner k F := by
  intro hF
  exact hG (hasStrictChainLength_mono_family hFG hF)

theorem hasStrictChainLength_of_succ
    {r : Nat} {F : Family α}
    (h : HasStrictChainLength (r + 1) F) :
    HasStrictChainLength r F := by
  cases r with
  | zero => trivial
  | succ d =>
      rcases h with ⟨B, hBF, A, hA, hAB⟩
      exact ⟨A, hA⟩

theorem hasStrictChainLength_of_le
    {r s : Nat} {F : Family α} (hrs : r ≤ s)
    (h : HasStrictChainLength s F) : HasStrictChainLength r F := by
  induction hrs with
  | refl => exact h
  | @step s hrs ih =>
      exact ih (hasStrictChainLength_of_succ h)

theorem isKSperner_mono_length
    {k l : Nat} {F : Family α} (hkl : k ≤ l)
    (hk : IsKSperner k F) : IsKSperner l F := by
  intro hl
  exact hk (hasStrictChainLength_of_le (Nat.add_le_add_right hkl 1) hl)

theorem isKSperner_iff (k : Nat) (F : Family α) :
    IsKSperner k F ↔ ¬ HasStrictChainLength (k + 1) F := by
  rfl

theorem isSaturatedKSperner_iff (k : Nat) (F : Family α) :
    IsSaturatedKSperner k F ↔
      (¬ HasStrictChainLength (k + 1) F) ∧
      ∀ S : Finset α, S ∉ F →
        HasStrictChainLength (k + 1) (insert S F) := by
  rfl

@[simp] theorem hasStrictChainLength_one_iff (F : Family α) :
    HasStrictChainLength 1 F ↔ F.Nonempty := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, hB⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, hB⟩

@[simp] theorem isKSperner_zero_iff (F : Family α) :
    IsKSperner 0 F ↔ F = ∅ := by
  simp [IsKSperner]

@[simp] theorem hasStrictChainLength_empty_iff (r : Nat) :
    HasStrictChainLength r (∅ : Family α) ↔ r = 0 := by
  cases r with
  | zero => simp
  | succ d =>
      simp only [Nat.succ_ne_zero, iff_false]
      rintro ⟨B, hB⟩
      simpa using hasStrictChainEndingAt_mem hB

@[simp] theorem isKSperner_empty (k : Nat) :
    IsKSperner k (∅ : Family α) := by
  intro h
  have := (hasStrictChainLength_empty_iff (α := α) (k + 1)).mp h
  omega

@[simp] theorem isSaturatedKSperner_zero_iff (F : Family α) :
    IsSaturatedKSperner 0 F ↔ F = ∅ := by
  constructor
  · exact fun h => (isKSperner_zero_iff F).mp h.1
  · rintro rfl
    refine ⟨isKSperner_empty 0, ?_⟩
    intro S hS
    exact (hasStrictChainLength_one_iff {S}).mpr (by simp)

@[simp] theorem isSaturatedKSperner_empty_iff (k : Nat) :
    IsSaturatedKSperner k (∅ : Family α) ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hins := h.2 (∅ : Finset α) (by simp)
    have htwo : HasStrictChainLength 2 ({∅} : Family α) :=
      hasStrictChainLength_of_le (by omega) hins
    simpa [HasStrictChainLength, HasStrictChainEndingAt] using htwo
  · rintro rfl
    exact (isSaturatedKSperner_zero_iff (∅ : Family α)).mpr rfl

@[simp] theorem not_hasNewStrictChainAt_of_mem
    {r : Nat} {F : Family α} {S : Finset α} (hSF : S ∈ F) :
    ¬ HasNewStrictChainAt r F S := by
  simp [HasNewStrictChainAt, Finset.insert_eq_of_mem hSF]

end AiMathLab.SaturatedSperner
