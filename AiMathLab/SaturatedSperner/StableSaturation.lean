import AiMathLab.SaturatedSperner.Equiv

/-!
# Eventual saturation numbers

This module records the exact finite-ground and eventual statements used by
P0054.  The eventual predicate includes both attainment and optimality on
every sufficiently large labelled ground `Fin n`; no separate stability
principle is assumed.
-/

universe u

namespace AiMathLab.SaturatedSperner

/-- `s` is the exact minimum size on the labelled `n`-point ground. -/
def IsSaturationNumberAt (k n s : Nat) : Prop :=
  (∃ F : Family (Fin n), IsSaturatedKSperner k F ∧ F.card = s) ∧
    ∀ F : Family (Fin n), IsSaturatedKSperner k F → s ≤ F.card

/-- `s` is the eventual stable saturation number for `k`-Sperner families. -/
def IsStableSaturationNumber (k s : Nat) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → IsSaturationNumberAt k n s

/-- Transporting a family along a ground equivalence preserves its size. -/
@[simp] theorem mapFamily_card
    {α β : Type u} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (F : Family α) :
    (mapFamily e F).card = F.card := by
  change (Finset.map e.finsetCongr.toEmbedding F).card = F.card
  exact Finset.card_map _

end AiMathLab.SaturatedSperner
