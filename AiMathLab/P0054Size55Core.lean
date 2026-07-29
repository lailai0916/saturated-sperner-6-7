/-
Copyright (c) 2026 AI Math Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhi Chen
-/
import AiMathLab.SaturatedSperner.Checker
import AiMathLab.SaturatedSperner.Layered

/-!
# A 55-member saturated 7-Sperner family

This file formalizes the explicit family discovered in P0054.  The ground set
is `Fin 11`; source labels `1,...,11` are represented by `0,...,10`.

The mathematical conclusion is expressed through the generic abstract
`IsSaturatedKSperner` predicate.  Executable checks are connected to that
predicate by the soundness theorem in `SaturatedSperner.Checker`.
-/

namespace AiMathLab.P0054

open AiMathLab.SaturatedSperner

/-- The eleven-point ground set of the smallest concrete realization. -/
abbrev Ground := Fin 11

/-- A subset of the ground set. -/
abbrev GroundSubset := Finset Ground

/-- A finite family of ground-set subsets. -/
abbrev Family := Finset GroundSubset

/-- Binary encoding of a subset.  Ground element `i` occupies bit `i`. -/
def subsetMask (S : GroundSubset) : Nat :=
  ∑ i ∈ S, 2 ^ i.val

/-- Decode an eleven-bit mask as a ground subset. -/
def maskSubset (m : Nat) : GroundSubset :=
  (Finset.univ : GroundSubset).filter fun i => m.testBit i.val

/-- The exact 55 masks in the frozen P0054 construction certificate. -/
def size55Masks : Finset Nat :=
  [0, 1, 2, 4, 32, 64, 10, 17, 20, 34, 72, 96, 129, 132,
    11, 14, 25, 28, 49, 52, 98, 193, 196, 30, 75, 180, 225, 94,
    1944, 1837, 1863, 1976, 2002, 1879, 1901, 1943, 1959, 1965,
    1978, 2010, 2040, 1911, 1917, 1967, 1979, 2007, 2013, 2030,
    2042, 1983, 2031, 2039, 2043, 2045, 2047].toFinset

/-- The explicit P0054 family on `Fin 11`. -/
def size55 : Family :=
  size55Masks.image maskSubset

set_option maxRecDepth 100000 in
theorem size55_card : size55.card = 55 := by
  decide

/-- A descending list of masks is a locally checkable strict chain. -/
def IsDescendingMaskChain : List Nat → Family → Prop
  | [], _ => False
  | [m], F => maskSubset m ∈ F
  | m :: a :: rest, F =>
      maskSubset m ∈ F ∧ IsDescendingMaskChain (a :: rest) F ∧
        maskSubset a ⊂ maskSubset m

/-- Executable checker for a descending mask chain. -/
def descendingMaskChainChecker : List Nat → Family → Bool
  | [], _ => false
  | [m], F => decide (maskSubset m ∈ F)
  | m :: a :: rest, F =>
      decide (maskSubset m ∈ F) && descendingMaskChainChecker (a :: rest) F &&
        decide (maskSubset a ⊂ maskSubset m)

theorem descendingMaskChainChecker_eq_true (w : List Nat) (F : Family) :
    descendingMaskChainChecker w F = true ↔ IsDescendingMaskChain w F := by
  induction w with
  | nil => simp [descendingMaskChainChecker, IsDescendingMaskChain]
  | cons m tail ih =>
      cases tail with
      | nil => simp [descendingMaskChainChecker, IsDescendingMaskChain]
      | cons a rest =>
          simp [descendingMaskChainChecker, IsDescendingMaskChain, ih, and_assoc]

theorem descendingMaskChain_sound (m : Nat) (tail : List Nat) (F : Family)
    (h : IsDescendingMaskChain (m :: tail) F) :
    HasStrictChainEndingAt tail.length F (maskSubset m) := by
  induction tail generalizing m with
  | nil => simpa [IsDescendingMaskChain, HasStrictChainEndingAt] using h
  | cons a rest ih =>
      simp only [IsDescendingMaskChain] at h
      exact ⟨h.1, maskSubset a, ih a h.2.1, h.2.2⟩

/-- A checked witness is an exact eight-member chain containing `S`. -/
def IsMaskChainWitness (r : Nat) (F : Family) (S : GroundSubset)
    (w : List Nat) : Prop :=
  w.length = r ∧ IsDescendingMaskChain w F ∧ S ∈ w.map maskSubset

theorem maskChainWitness_sound {r : Nat} {F : Family} {S : GroundSubset}
    {w : List Nat} (h : IsMaskChainWitness r F S w) :
    HasStrictChainLength r F := by
  rcases h with ⟨hlen, hchain, _⟩
  rcases w with _ | ⟨m, tail⟩
  · simp [IsDescendingMaskChain] at hchain
  · rw [← hlen]
    exact ⟨maskSubset m, descendingMaskChain_sound m tail F hchain⟩

/-- Boolean checker for one explicit chain witness. -/
def maskChainWitnessChecker (r : Nat) (F : Family) (S : GroundSubset)
    (w : List Nat) : Bool :=
  decide (w.length = r) && descendingMaskChainChecker w F &&
    decide (S ∈ w.map maskSubset)

theorem maskChainWitnessChecker_eq_true (r : Nat) (F : Family)
    (S : GroundSubset) (w : List Nat) :
    maskChainWitnessChecker r F S w = true ↔ IsMaskChainWitness r F S w := by
  simp [maskChainWitnessChecker, IsMaskChainWitness,
    descendingMaskChainChecker_eq_true, and_assoc]

/-- The seven P0054 layers in increasing order. -/
def size55LayerMasks : List (List Nat) := [
  [0],
  [1, 2, 4, 32, 64, 1944],
  [10, 17, 20, 34, 72, 96, 129, 132, 1837, 1863, 1976, 2002],
  [11, 14, 25, 28, 49, 52, 98, 193, 196, 1879, 1901, 1943, 1959,
    1965, 1978, 2010, 2040],
  [30, 75, 180, 225, 1911, 1917, 1967, 1979, 2007, 2013, 2030, 2042],
  [94, 1983, 2031, 2039, 2043, 2045],
  [2047]
]

/-- The seven displayed layers have the certified sizes `1,6,12,17,12,6,1`. -/
theorem size55LayerMasks_sizes : size55LayerMasks.map List.length = [1, 6, 12, 17, 12, 6, 1] := by
  decide

/-- The displayed layers contain exactly the masks defining `size55`. -/
theorem size55LayerMasks_crosswalk : size55LayerMasks.flatten.toFinset = size55Masks := by
  decide

/-- The seven explicit layers as finite families on `Fin 11`. -/
def size55Layers (i : Fin 7) : Family :=
  ((size55LayerMasks.getD i.val []).toFinset).image maskSubset

theorem size55_layerUnion : LayerUnion size55Layers = size55 := by
  decide

private theorem size55Layers_antichain : ∀ i, IsAntichain (size55Layers i) := by
  intro i
  fin_cases i <;> exact isKSpernerChecker_sound (by decide)

/-- Seven antichain layers cannot contain a strict chain of eight members. -/
theorem size55_seven_sperner : IsKSperner 7 size55 := by
  rw [← size55_layerUnion]
  exact layerUnion_isKSperner size55Layers size55Layers_antichain

/-- Encoding and decoding are inverse on eleven-point ground subsets. -/
theorem maskSubset_subsetMask (S : GroundSubset) :
    maskSubset (subsetMask S) = S := by
  have hsum : subsetMask S = ∑ j ∈ S.image Fin.val, 2 ^ j := by
    rw [subsetMask, Finset.sum_image]
    exact Fin.val_injective.injOn
  have hbits := Finset.toFinset_bitIndices_sum_two_pow (S.image Fin.val)
  rw [← hsum] at hbits
  ext i
  simp only [maskSubset, Finset.mem_filter, Finset.mem_univ, true_and,
    ← Nat.mem_bitIndices, ← List.mem_toFinset, hbits, Finset.mem_image]
  exact ⟨fun ⟨j, hj, hji⟩ => Fin.val_injective hji ▸ hj,
    fun hi => ⟨i, hi, rfl⟩⟩

/-- Every encoded subset is an eleven-bit mask. -/
theorem subsetMask_lt_2048 (S : GroundSubset) : subsetMask S < 2048 := by
  have hsum : subsetMask S = ∑ j ∈ S.image Fin.val, 2 ^ j := by
    rw [subsetMask, Finset.sum_image]
    exact Fin.val_injective.injOn
  rw [hsum]
  simpa using Nat.geomSum_lt (s := S.image Fin.val) (m := 2) (n := 11)
    (by omega) (by simp)

end AiMathLab.P0054
