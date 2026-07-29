/-
Copyright (c) 2026 AI Math Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI Math Lab
-/
import Mathlib

/-!
# The published 56-member saturated 7-Sperner family

This file formalizes the `|H| = 3`, `n = 10` instance of the construction on
printed pages 7--9 of Martin--Veldt, *Electronic Journal of Combinatorics*
32(1) (2025), #P1.55.

The mathematical predicates below are propositions.  The executable checkers
are separate definitions, connected to those predicates by proved equivalences.
-/

namespace AiMathLab.P0053

/-- The ten-point ground set.  `Fin 10` uses labels `0,...,9`; source label
`j` is represented by `j - 1`. -/
abbrev Ground := Fin 10

/-- A subset of the ground set. -/
abbrev GroundSubset := Finset Ground

/-- A finite family of ground-set subsets. -/
abbrev Family := Finset GroundSubset

/-- `HasStrictChainEndingAt d F B` says that `F` has a strict-inclusion chain
of length `d + 1` whose final member is `B`.  This is an abstract proposition,
not a Boolean checker. -/
def HasStrictChainEndingAt : Nat → Family → GroundSubset → Prop
  | 0, F, B => B ∈ F
  | d + 1, F, B => B ∈ F ∧ ∃ A, HasStrictChainEndingAt d F A ∧ A ⊂ B

/-- The family contains a strict-inclusion chain with exactly `r` members.
The empty chain witnesses the case `r = 0`. -/
def HasStrictChainLength : Nat → Family → Prop
  | 0, _ => True
  | d + 1, F => ∃ B, HasStrictChainEndingAt d F B

/-- An `r`-chain in `F` passes through `S`: such a chain exists, while erasing
`S` destroys every `r`-chain.  In the saturation application the old family
has no forbidden chain, so this is equivalent to saying that the new chain
created by inserting `S` contains `S`. -/
def HasStrictChainThrough (r : Nat) (F : Family) (S : GroundSubset) : Prop :=
  HasStrictChainLength r F ∧ ¬ HasStrictChainLength r (F.erase S)

/-- A family is `k`-Sperner when it has no strict chain of length `k + 1`. -/
def IsKSperner (k : Nat) (F : Family) : Prop :=
  ¬ HasStrictChainLength (k + 1) F

/-- A saturated `k`-Sperner family is itself `k`-Sperner and inserting every
external ground subset creates a strict `(k + 1)`-chain through that subset. -/
def IsSaturatedKSperner (k : Nat) (F : Family) : Prop :=
  IsKSperner k F ∧
    ∀ S : GroundSubset, S ∉ F →
      HasStrictChainThrough (k + 1) (insert S F) S

/-- Dynamic-programming endpoints: `chainEnds d F` contains precisely the
possible final members of strict chains of length `d + 1` in `F`. -/
def chainEnds : Nat → Family → Family
  | 0, F => F
  | d + 1, F =>
      F.filter fun B => ∃ A ∈ chainEnds d F, A ⊂ B

theorem mem_chainEnds_iff (d : Nat) (F : Family) (B : GroundSubset) :
    B ∈ chainEnds d F ↔ HasStrictChainEndingAt d F B := by
  induction d generalizing B with
  | zero => simp [chainEnds, HasStrictChainEndingAt]
  | succ d ih =>
      simp only [chainEnds, Finset.mem_filter, HasStrictChainEndingAt]
      constructor
      · rintro ⟨hBF, A, hA, hAB⟩
        exact ⟨hBF, A, (ih A).mp hA, hAB⟩
      · rintro ⟨hBF, A, hA, hAB⟩
        exact ⟨hBF, A, (ih A).mpr hA, hAB⟩

/-- Executable checker for a strict chain of a prescribed length. -/
def hasStrictChainChecker : Nat → Family → Bool
  | 0, _ => true
  | d + 1, F => decide (chainEnds d F).Nonempty

theorem hasStrictChainChecker_eq_true (r : Nat) (F : Family) :
    hasStrictChainChecker r F = true ↔ HasStrictChainLength r F := by
  cases r with
  | zero => simp [hasStrictChainChecker, HasStrictChainLength]
  | succ d =>
      simp only [hasStrictChainChecker, decide_eq_true_eq, HasStrictChainLength]
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨B, (mem_chainEnds_iff d F B).mp hB⟩
      · rintro ⟨B, hB⟩
        exact ⟨B, (mem_chainEnds_iff d F B).mpr hB⟩

/-- Executable checker for the `k`-Sperner predicate. -/
def isKSpernerChecker (k : Nat) (F : Family) : Bool :=
  !(hasStrictChainChecker (k + 1) F)

theorem isKSpernerChecker_eq_true (k : Nat) (F : Family) :
    isKSpernerChecker k F = true ↔ IsKSperner k F := by
  unfold isKSpernerChecker IsKSperner
  have hiff := hasStrictChainChecker_eq_true (k + 1) F
  cases hcheck : hasStrictChainChecker (k + 1) F <;>
    simp [hcheck] at hiff ⊢
  all_goals exact hiff

/-- Executable saturation checker.  The `all` traverses all `2^10` ground
subsets; no sampling or restricted outside-set list is used. -/
def isSaturatedKSpernerChecker (k : Nat) (F : Family) : Bool :=
  isKSpernerChecker k F &&
    decide (∀ S : GroundSubset,
      S ∈ F ∨ hasStrictChainChecker (k + 1) (insert S F) = true)

theorem isSaturatedKSpernerChecker_eq_true (k : Nat) (F : Family) :
    isSaturatedKSpernerChecker k F = true ↔ IsSaturatedKSperner k F := by
  rw [isSaturatedKSpernerChecker, Bool.and_eq_true]
  rw [isKSpernerChecker_eq_true]
  simp only [decide_eq_true_eq, hasStrictChainChecker_eq_true]
  constructor
  · rintro ⟨hk, hall⟩
    refine ⟨hk, ?_⟩
    intro S hSF
    have hins : HasStrictChainLength (k + 1) (insert S F) := by
      rcases hall S with hmem | hchain
      · exact False.elim (hSF hmem)
      · exact hchain
    refine ⟨hins, ?_⟩
    simpa [IsKSperner, Finset.erase_insert, hSF] using hk
  · rintro ⟨hk, hsaturated⟩
    refine ⟨hk, ?_⟩
    intro S
    by_cases hSF : S ∈ F
    · exact Or.inl hSF
    · exact Or.inr (hsaturated S hSF).1

/-- Binary encoding of a ground subset.  Source label `j` occupies bit
`j - 1`, matching the frozen JSON and Python certificate. -/
def subsetMask (S : GroundSubset) : Nat :=
  ∑ i ∈ S, 2 ^ i.val

/-- The 56 canonical masks in the frozen published certificate. -/
def published56Masks : Finset Nat :=
  [0, 2, 4, 16, 32, 64, 3, 6, 12, 24, 48, 65, 96, 13, 26, 35, 52, 70,
    81, 104, 43, 45, 53, 85, 86, 90, 106, 118, 905, 917, 933, 937, 938,
    970, 978, 980, 919, 942, 953, 971, 988, 997, 1010, 927, 958, 975,
    999, 1011, 1017, 1020, 959, 991, 1007, 1019, 1021, 1023].toFinset

/-- The published `H = {8,9,10}` family, with source labels shifted down by
one to inhabit `Fin 10`. -/
def published56 : Family :=
  (Finset.univ : Family).filter fun S => subsetMask S ∈ published56Masks

set_option maxRecDepth 100000 in
theorem published56_card : published56.card = 56 := by
  decide

set_option maxRecDepth 100000 in
theorem published56_seven_sperner :
    IsKSperner 7 published56 := by
  exact (isKSpernerChecker_eq_true 7 published56).mp (by decide)

/-- Decode a ten-bit mask as a ground subset. -/
def maskSubset (m : Nat) : GroundSubset :=
  (Finset.univ : GroundSubset).filter fun i => m.testBit i.val

/-- A descending list of masks is a locally checkable strict chain.  Storing
the greatest member first makes this predicate follow the recursive abstract
`HasStrictChainEndingAt` definition exactly. -/
def IsDescendingMaskChain : List Nat → Family → Prop
  | [], _ => False
  | [m], F => maskSubset m ∈ F
  | m :: a :: rest, F =>
      maskSubset m ∈ F ∧ IsDescendingMaskChain (a :: rest) F ∧
        maskSubset a ⊂ maskSubset m

/-- Executable local checker for a descending mask chain. -/
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

/-- An explicit witness consists of exactly `r` masks forming a descending
strict chain in `F`, and its decoded members include the required set `S`. -/
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

/- The table declaration is generated below from the frozen source certificate.
Every entry is checked inside Lean; the generator is not trusted. -/
/- The concrete witness generator uses only the seven frozen source layers.  Its
choices are not trusted: the checker below validates the generated chain for
every ground subset inside Lean. -/

/-- The seven source layers, in increasing canonical-decomposition order. -/
def published56LayerMasks : List (List Nat) := [
  [0],
  [2, 4, 16, 32, 64, 905],
  [3, 6, 12, 24, 48, 96, 65, 980, 937, 978, 933, 970, 917, 938],
  [35, 70, 13, 26, 52, 104, 81, 988, 953, 1010, 997, 971, 919, 942],
  [1020, 1017, 1011, 999, 975, 927, 958, 43, 86, 45, 90, 53, 106, 85],
  [1021, 1019, 1007, 991, 959, 118],
  [1023]
]

/-- The first member of a layer strictly below the requested subset. -/
def firstBelow (layer : List Nat) (S : GroundSubset) : Option Nat :=
  layer.find? fun m => decide (maskSubset m ⊂ S)

/-- The first member of a layer strictly above the requested subset. -/
def firstAbove (layer : List Nat) (S : GroundSubset) : Option Nat :=
  layer.find? fun m => decide (S ⊂ maskSubset m)

/-- Starting in source layer `level`, choose one predecessor from each earlier
layer.  The result is stored in descending order. -/
def descendWitness : Nat → Nat → List Nat
  | 0, m => [m]
  | level + 1, m =>
      let previousLayer := published56LayerMasks.getD level []
      let previous :=
        (previousLayer.find? fun a =>
          decide (maskSubset a ⊂ maskSubset m)).getD 0
      m :: descendWitness level previous

/-- Choose one successor from each later layer.  This helper returns ascending
order; callers reverse it to obtain the certificate's descending convention. -/
def ascendWitness : Nat → Nat → Nat → List Nat
  | 0, _, m => [m]
  | fuel + 1, level, m =>
      let nextLayer := published56LayerMasks.getD (level + 1) []
      let next :=
        (nextLayer.find? fun b =>
          decide (maskSubset m ⊂ maskSubset b)).getD 0
      m :: ascendWitness fuel (level + 1) next

/-- Search source layers from high to low for the longest lower chain. -/
def lowerWitnessSearch : Nat → GroundSubset → List Nat
  | 0, S =>
      match firstBelow (published56LayerMasks.getD 0 []) S with
      | some m => descendWitness 0 m
      | none => []
  | level + 1, S =>
      match firstBelow (published56LayerMasks.getD (level + 1) []) S with
      | some m => descendWitness (level + 1) m
      | none => lowerWitnessSearch level S

/-- Search source layers from low to high for the longest upper chain. -/
def upperWitnessSearch : Nat → Nat → GroundSubset → List Nat
  | 0, level, S =>
      match firstAbove (published56LayerMasks.getD level []) S with
      | some m => (ascendWitness (6 - level) level m).reverse
      | none => []
  | fuel + 1, level, S =>
      match firstAbove (published56LayerMasks.getD level []) S with
      | some m => (ascendWitness (6 - level) level m).reverse
      | none => upperWitnessSearch fuel (level + 1) S

/-- Deterministically generate a candidate descending eight-chain through
`S`: an upper chain, then `S`, then a lower chain. -/
def published56Witness (S : GroundSubset) : List Nat :=
  upperWitnessSearch 6 0 S ++
    subsetMask S :: lowerWitnessSearch 6 S

/-- Executable local checker for the generated witness. -/
def published56WitnessChecker (S : GroundSubset) : Bool :=
  maskChainWitnessChecker 8 (insert S published56) S (published56Witness S)

/-- Encoding and decoding are inverse on ten-point ground subsets. -/
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

/-- Every encoded ground subset is a ten-bit mask. -/
theorem subsetMask_lt_1024 (S : GroundSubset) : subsetMask S < 1024 := by
  have hsum : subsetMask S = ∑ j ∈ S.image Fin.val, 2 ^ j := by
    rw [subsetMask, Finset.sum_image]
    exact Fin.val_injective.injOn
  rw [hsum]
  simpa using Nat.geomSum_lt (s := S.image Fin.val) (m := 2) (n := 10)
    (by omega) (by simp)

/-- A block checker verifies 64 consecutive masks. -/
def published56WitnessBlockChecker (lo : Nat) : Bool :=
  decide (∀ i : Fin 64,
    let S := maskSubset (lo + i.val)
    S ∈ published56 ∨ published56WitnessChecker S = true)

theorem published56WitnessBlockChecker_eq_true (lo : Nat) :
    published56WitnessBlockChecker lo = true ↔
      ∀ i : Fin 64,
        let S := maskSubset (lo + i.val)
        S ∈ published56 ∨ published56WitnessChecker S = true := by
  simp [published56WitnessBlockChecker]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_00 :
    published56WitnessBlockChecker 0 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_01 :
    published56WitnessBlockChecker 64 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_02 :
    published56WitnessBlockChecker 128 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_03 :
    published56WitnessBlockChecker 192 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_04 :
    published56WitnessBlockChecker 256 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_05 :
    published56WitnessBlockChecker 320 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_06 :
    published56WitnessBlockChecker 384 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_07 :
    published56WitnessBlockChecker 448 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_08 :
    published56WitnessBlockChecker 512 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_09 :
    published56WitnessBlockChecker 576 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_10 :
    published56WitnessBlockChecker 640 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_11 :
    published56WitnessBlockChecker 704 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_12 :
    published56WitnessBlockChecker 768 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_13 :
    published56WitnessBlockChecker 832 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_14 :
    published56WitnessBlockChecker 896 = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem published56_witness_block_15 :
    published56WitnessBlockChecker 960 = true := by
  decide
/-- The sixteen opaque blocks cover exactly masks `0,...,1023`. -/
private theorem published56_witness_masks_complete (m : Nat) (hm : m < 1024) :
    let S := maskSubset m
    S ∈ published56 ∨ published56WitnessChecker S = true := by
  by_cases h00 : m < 64
  · have h := (published56WitnessBlockChecker_eq_true 0).mp
      published56_witness_block_00 ⟨m - 0, by omega⟩
    have heq : 0 + (m - 0) = m := by omega
    simpa only [heq] using h
  by_cases h01 : m < 128
  · have h := (published56WitnessBlockChecker_eq_true 64).mp
      published56_witness_block_01 ⟨m - 64, by omega⟩
    have heq : 64 + (m - 64) = m := by omega
    simpa only [heq] using h
  by_cases h02 : m < 192
  · have h := (published56WitnessBlockChecker_eq_true 128).mp
      published56_witness_block_02 ⟨m - 128, by omega⟩
    have heq : 128 + (m - 128) = m := by omega
    simpa only [heq] using h
  by_cases h03 : m < 256
  · have h := (published56WitnessBlockChecker_eq_true 192).mp
      published56_witness_block_03 ⟨m - 192, by omega⟩
    have heq : 192 + (m - 192) = m := by omega
    simpa only [heq] using h
  by_cases h04 : m < 320
  · have h := (published56WitnessBlockChecker_eq_true 256).mp
      published56_witness_block_04 ⟨m - 256, by omega⟩
    have heq : 256 + (m - 256) = m := by omega
    simpa only [heq] using h
  by_cases h05 : m < 384
  · have h := (published56WitnessBlockChecker_eq_true 320).mp
      published56_witness_block_05 ⟨m - 320, by omega⟩
    have heq : 320 + (m - 320) = m := by omega
    simpa only [heq] using h
  by_cases h06 : m < 448
  · have h := (published56WitnessBlockChecker_eq_true 384).mp
      published56_witness_block_06 ⟨m - 384, by omega⟩
    have heq : 384 + (m - 384) = m := by omega
    simpa only [heq] using h
  by_cases h07 : m < 512
  · have h := (published56WitnessBlockChecker_eq_true 448).mp
      published56_witness_block_07 ⟨m - 448, by omega⟩
    have heq : 448 + (m - 448) = m := by omega
    simpa only [heq] using h
  by_cases h08 : m < 576
  · have h := (published56WitnessBlockChecker_eq_true 512).mp
      published56_witness_block_08 ⟨m - 512, by omega⟩
    have heq : 512 + (m - 512) = m := by omega
    simpa only [heq] using h
  by_cases h09 : m < 640
  · have h := (published56WitnessBlockChecker_eq_true 576).mp
      published56_witness_block_09 ⟨m - 576, by omega⟩
    have heq : 576 + (m - 576) = m := by omega
    simpa only [heq] using h
  by_cases h10 : m < 704
  · have h := (published56WitnessBlockChecker_eq_true 640).mp
      published56_witness_block_10 ⟨m - 640, by omega⟩
    have heq : 640 + (m - 640) = m := by omega
    simpa only [heq] using h
  by_cases h11 : m < 768
  · have h := (published56WitnessBlockChecker_eq_true 704).mp
      published56_witness_block_11 ⟨m - 704, by omega⟩
    have heq : 704 + (m - 704) = m := by omega
    simpa only [heq] using h
  by_cases h12 : m < 832
  · have h := (published56WitnessBlockChecker_eq_true 768).mp
      published56_witness_block_12 ⟨m - 768, by omega⟩
    have heq : 768 + (m - 768) = m := by omega
    simpa only [heq] using h
  by_cases h13 : m < 896
  · have h := (published56WitnessBlockChecker_eq_true 832).mp
      published56_witness_block_13 ⟨m - 832, by omega⟩
    have heq : 832 + (m - 832) = m := by omega
    simpa only [heq] using h
  by_cases h14 : m < 960
  · have h := (published56WitnessBlockChecker_eq_true 896).mp
      published56_witness_block_14 ⟨m - 896, by omega⟩
    have heq : 896 + (m - 896) = m := by omega
    simpa only [heq] using h
  · have h := (published56WitnessBlockChecker_eq_true 960).mp
      published56_witness_block_15 ⟨m - 960, by omega⟩
    have heq : 960 + (m - 960) = m := by omega
    simpa only [heq] using h

/-- The greedy generator is checked on all `2^10 = 1024` subsets.  The 56
family members discharge the left disjunct; all 968 external subsets have an
eight-mask certificate checked by `published56WitnessChecker`. -/
private theorem published56_witness_generator_complete :
    ∀ S : GroundSubset,
      S ∈ published56 ∨ published56WitnessChecker S = true := by
  intro S
  have h := published56_witness_masks_complete (subsetMask S) (subsetMask_lt_1024 S)
  simpa only [maskSubset_subsetMask] using h

set_option maxRecDepth 100000 in
theorem published56_saturated :
    IsSaturatedKSperner 7 published56 := by
  refine ⟨published56_seven_sperner, ?_⟩
  intro S hSF
  have hchecked : published56WitnessChecker S = true :=
    (published56_witness_generator_complete S).resolve_left hSF
  have hwitness : IsMaskChainWitness 8 (insert S published56) S
      (published56Witness S) :=
    (maskChainWitnessChecker_eq_true 8 (insert S published56) S
      (published56Witness S)).mp hchecked
  refine ⟨maskChainWitness_sound hwitness, ?_⟩
  simpa [IsKSperner, Finset.erase_insert, hSF] using
    published56_seven_sperner

theorem published56_full_certificate :
    published56.card = 56 ∧ IsSaturatedKSperner 7 published56 :=
  ⟨published56_card, published56_saturated⟩




end AiMathLab.P0053
