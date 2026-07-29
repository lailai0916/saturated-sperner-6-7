import AiMathLab.SaturatedSperner.Layered

/-!
# Canonical decomposition of finite set families

The canonical layers are obtained by repeatedly removing the
inclusion-minimal members of the current remainder.  All results in this file
are symbolic over the ground type; only decidable equality is required.
-/

universe u

namespace AiMathLab.SaturatedSperner

variable {α : Type u} [DecidableEq α]

/-- The inclusion-minimal members of a finite family. -/
def minimalMembers (F : Family α) : Family α :=
  F.filter fun S => ∀ T ∈ F, ¬ T ⊂ S

/-- The family left after removing the first `i` canonical layers. -/
def canonicalRemainder (F : Family α) : Nat → Family α
  | 0 => F
  | i + 1 =>
      canonicalRemainder F i \
        minimalMembers (canonicalRemainder F i)

/-- The `i`-th canonical layer. -/
def canonicalLayer (F : Family α) (i : Nat) : Family α :=
  minimalMembers (canonicalRemainder F i)

/-- The first `k` canonical layers, indexed from bottom to top. -/
def canonicalLayers (k : Nat) (F : Family α) : Fin k → Family α :=
  fun i => canonicalLayer F i.val

@[simp] theorem mem_minimalMembers
    (F : Family α) (S : Finset α) :
    S ∈ minimalMembers F ↔
      S ∈ F ∧ ∀ T ∈ F, ¬ T ⊂ S := by
  simp [minimalMembers]

theorem minimalMembers_subset (F : Family α) :
    minimalMembers F ⊆ F := by
  intro S hS
  exact (mem_minimalMembers F S).mp hS |>.1

theorem exists_minimalMember_subset
    (F : Family α) {D : Finset α} (hD : D ∈ F) :
    ∃ C : Finset α, C ∈ minimalMembers F ∧ C ⊆ D := by
  induction D using Finset.strongInduction with
  | _ D ih =>
      by_cases hminimal : ∀ T ∈ F, ¬ T ⊂ D
      · exact ⟨D, (mem_minimalMembers F D).mpr ⟨hD, hminimal⟩,
          Finset.Subset.rfl⟩
      · push Not at hminimal
        rcases hminimal with ⟨T, hTF, hTD⟩
        rcases ih T hTD hTF with ⟨C, hC, hCT⟩
        exact ⟨C, hC, hCT.trans hTD.1⟩

theorem minimalMembers_nonempty_iff (F : Family α) :
    (minimalMembers F).Nonempty ↔ F.Nonempty := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S, minimalMembers_subset F hS⟩
  · rintro ⟨D, hD⟩
    rcases exists_minimalMember_subset F hD with ⟨C, hC, hCD⟩
    exact ⟨C, hC⟩

@[simp] theorem canonicalRemainder_zero (F : Family α) :
    canonicalRemainder F 0 = F := by
  rfl

@[simp] theorem canonicalRemainder_succ
    (F : Family α) (i : Nat) :
    canonicalRemainder F (i + 1) =
      canonicalRemainder F i \ canonicalLayer F i := by
  rfl

@[simp] theorem mem_canonicalLayer
    (F : Family α) (i : Nat) (S : Finset α) :
    S ∈ canonicalLayer F i ↔
      S ∈ canonicalRemainder F i ∧
        ∀ T ∈ canonicalRemainder F i, ¬ T ⊂ S := by
  exact mem_minimalMembers _ _

@[simp] theorem mem_canonicalRemainder_succ_iff
    (F : Family α) (i : Nat) (S : Finset α) :
    S ∈ canonicalRemainder F (i + 1) ↔
      S ∈ canonicalRemainder F i ∧
        S ∉ canonicalLayer F i := by
  simp [canonicalRemainder_succ]

theorem canonicalRemainder_succ_subset
    (F : Family α) (i : Nat) :
    canonicalRemainder F (i + 1) ⊆ canonicalRemainder F i := by
  rw [canonicalRemainder_succ]
  exact Finset.sdiff_subset

theorem canonicalRemainder_antitone
    (F : Family α) {i j : Nat} (hij : i ≤ j) :
    canonicalRemainder F j ⊆ canonicalRemainder F i := by
  induction hij with
  | refl => exact Finset.Subset.rfl
  | @step j hij ih =>
      exact (canonicalRemainder_succ_subset F j).trans ih

theorem mem_canonicalRemainder_iff
    (F : Family α) (n : Nat) (S : Finset α) :
    S ∈ canonicalRemainder F n ↔
      S ∈ F ∧ ∀ i : Nat, i < n → S ∉ canonicalLayer F i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [mem_canonicalRemainder_succ_iff, ih]
      constructor
      · rintro ⟨⟨hSF, hall⟩, hn⟩
        refine ⟨hSF, ?_⟩
        intro i hi
        by_cases hin : i = n
        · simpa [hin] using hn
        · exact hall i (by omega)
      · rintro ⟨hSF, hall⟩
        exact ⟨⟨hSF, fun i hi => hall i (by omega)⟩,
          hall n (by omega)⟩

theorem canonicalRemainder_eq_sdiff_layerUnion
    (F : Family α) (n : Nat) :
    canonicalRemainder F n =
      F \ LayerUnion (canonicalLayers n F) := by
  ext S
  rw [mem_canonicalRemainder_iff]
  simp only [Finset.mem_sdiff, mem_layerUnion]
  constructor
  · rintro ⟨hSF, hall⟩
    refine ⟨hSF, ?_⟩
    rintro ⟨i, hi⟩
    exact hall i.val i.isLt hi
  · rintro ⟨hSF, hnone⟩
    refine ⟨hSF, ?_⟩
    intro i hi hiS
    exact hnone ⟨⟨i, hi⟩, hiS⟩

theorem canonicalLayer_subset_remainder
    (F : Family α) (i : Nat) :
    canonicalLayer F i ⊆ canonicalRemainder F i :=
  minimalMembers_subset _

theorem canonicalRemainder_subset
    (F : Family α) (i : Nat) :
    canonicalRemainder F i ⊆ F := by
  exact canonicalRemainder_antitone F (Nat.zero_le i)

theorem canonicalLayer_subset
    (F : Family α) (i : Nat) :
    canonicalLayer F i ⊆ F :=
  (canonicalLayer_subset_remainder F i).trans
    (canonicalRemainder_subset F i)

theorem canonicalRemainder_succ_ssubset
    (F : Family α) (i : Nat)
    (hrem : (canonicalRemainder F i).Nonempty) :
    canonicalRemainder F (i + 1) ⊂ canonicalRemainder F i := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨canonicalRemainder_succ_subset F i, ?_⟩
  intro heq
  have hlayer : (canonicalLayer F i).Nonempty :=
    (minimalMembers_nonempty_iff _).mpr hrem
  rcases hlayer with ⟨S, hS⟩
  have hSrem := canonicalLayer_subset_remainder F i hS
  have hSnext : S ∈ canonicalRemainder F (i + 1) := by
    rw [heq]
    exact hSrem
  exact (mem_canonicalRemainder_succ_iff F i S).mp hSnext |>.2 hS

theorem canonicalRemainder_card_lt
    (F : Family α) (i : Nat)
    (hrem : (canonicalRemainder F i).Nonempty) :
    (canonicalRemainder F (i + 1)).card <
      (canonicalRemainder F i).card :=
  Finset.card_lt_card (canonicalRemainder_succ_ssubset F i hrem)

theorem canonicalRemainder_card_bound_of_nonempty
    (F : Family α) {n : Nat}
    (hn : (canonicalRemainder F n).Nonempty) :
    n + (canonicalRemainder F n).card ≤ F.card := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev : (canonicalRemainder F n).Nonempty := by
        rcases hn with ⟨S, hS⟩
        exact ⟨S, canonicalRemainder_succ_subset F n hS⟩
      have hbound := ih hprev
      have hcard := canonicalRemainder_card_lt F n hprev
      omega

@[simp] theorem canonicalRemainder_card_eq_empty (F : Family α) :
    canonicalRemainder F F.card = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  have hbound := canonicalRemainder_card_bound_of_nonempty F hne
  have hpos := Finset.card_pos.mpr hne
  omega

theorem canonicalRemainder_eq_empty_of_card_le
    (F : Family α) {n : Nat} (hcard : F.card ≤ n) :
    canonicalRemainder F n = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨S, hS⟩
  have hsub := canonicalRemainder_antitone F hcard hS
  simpa using hsub

theorem canonicalLayer_succ_predecessor
    (F : Family α) (i : Nat) {D : Finset α}
    (hD : D ∈ canonicalLayer F (i + 1)) :
    ∃ C : Finset α, C ∈ canonicalLayer F i ∧ C ⊂ D := by
  have hDnext := canonicalLayer_subset_remainder F (i + 1) hD
  have hDstep := (mem_canonicalRemainder_succ_iff F i D).mp hDnext
  rcases exists_minimalMember_subset
      (canonicalRemainder F i) hDstep.1 with ⟨C, hC, hCD⟩
  refine ⟨C, hC, Finset.ssubset_iff_subset_ne.mpr ⟨hCD, ?_⟩⟩
  intro hEq
  subst C
  exact hDstep.2 hC

theorem minimalMembers_antichain (F : Family α) :
    IsAntichain (minimalMembers F) := by
  rintro ⟨B, hB, A, hA, hAB⟩
  exact (mem_minimalMembers F B).mp hB |>.2 A
    (minimalMembers_subset F hA) hAB

theorem canonicalLayers_antichain
    (k : Nat) (F : Family α) :
    ∀ i : Fin k, IsAntichain (canonicalLayers k F i) := by
  intro i
  exact minimalMembers_antichain _

theorem canonicalLayers_pairwiseDisjoint
    (k : Nat) (F : Family α) :
    PairwiseDisjointLayers (canonicalLayers k F) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro S hiS hjS
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hjrem := canonicalLayer_subset_remainder F j.val hjS
    have hnext : S ∈ canonicalRemainder F (i.val + 1) :=
      canonicalRemainder_antitone F (by omega) hjrem
    exact (mem_canonicalRemainder_succ_iff F i.val S).mp hnext |>.2 hiS
  · have hirem := canonicalLayer_subset_remainder F i.val hiS
    have hnext : S ∈ canonicalRemainder F (j.val + 1) :=
      canonicalRemainder_antitone F (by omega) hirem
    exact (mem_canonicalRemainder_succ_iff F j.val S).mp hnext |>.2 hjS

theorem canonicalLayers_layered
    (k : Nat) (F : Family α) :
    IsLayered (canonicalLayers k F) := by
  intro i hi D hD
  exact canonicalLayer_succ_predecessor F i hD

theorem canonicalLayer_index_lt_of_ssubset
    (F : Family α) {i j : Nat} {C D : Finset α}
    (hC : C ∈ canonicalLayer F i)
    (hD : D ∈ canonicalLayer F j)
    (hCD : C ⊂ D) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  have hCremi := canonicalLayer_subset_remainder F i hC
  have hCremj := canonicalRemainder_antitone F hji hCremi
  exact (mem_canonicalLayer F j D).mp hD |>.2 C hCremj hCD

theorem canonicalLayer_hasStrictChainEndingAt
    (F : Family α) {i : Nat} {D : Finset α}
    (hD : D ∈ canonicalLayer F i) :
    HasStrictChainEndingAt i F D := by
  induction i generalizing D with
  | zero => exact canonicalLayer_subset F 0 hD
  | succ i ih =>
      rcases canonicalLayer_succ_predecessor F i hD with ⟨C, hC, hCD⟩
      exact ⟨canonicalLayer_subset F (i + 1) hD, C, ih hC, hCD⟩

theorem canonicalRemainder_eq_empty_of_isKSperner
    {k : Nat} {F : Family α} (hsp : IsKSperner k F) :
    canonicalRemainder F k = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hrem
  have hlayer : (canonicalLayer F k).Nonempty :=
    (minimalMembers_nonempty_iff _).mpr hrem
  rcases hlayer with ⟨D, hD⟩
  exact hsp ⟨D, canonicalLayer_hasStrictChainEndingAt F hD⟩

theorem canonicalLayers_cover_of_isKSperner
    {k : Nat} {F : Family α} (hsp : IsKSperner k F) :
    F ⊆ LayerUnion (canonicalLayers k F) := by
  intro S hSF
  by_contra hnot
  have hrem : S ∈ canonicalRemainder F k :=
    (mem_canonicalRemainder_iff F k S).mpr ⟨hSF, by
      intro i hi hiS
      exact hnot ((mem_layerUnion (canonicalLayers k F) S).mpr
        ⟨⟨i, hi⟩, hiS⟩)⟩
  rw [canonicalRemainder_eq_empty_of_isKSperner hsp] at hrem
  simpa using hrem

theorem layerUnion_canonicalLayers_subset
    (k : Nat) (F : Family α) :
    LayerUnion (canonicalLayers k F) ⊆ F := by
  intro S hS
  rcases (mem_layerUnion (canonicalLayers k F) S).mp hS with ⟨i, hi⟩
  exact canonicalLayer_subset F i.val hi

theorem layerUnion_canonicalLayers_eq
    {k : Nat} {F : Family α} (hsp : IsKSperner k F) :
    LayerUnion (canonicalLayers k F) = F := by
  apply Finset.Subset.antisymm
  · exact layerUnion_canonicalLayers_subset k F
  · exact canonicalLayers_cover_of_isKSperner hsp

theorem strictChain_uses_each_canonical_layer
    {k : Nat} {F : Family α}
    (hsp : IsKSperner k F)
    (f : Fin k → Finset α)
    (hmem : ∀ i, f i ∈ F)
    (hstrict : StrictMono f) :
    ∀ i j : Fin k,
      f i ∈ canonicalLayers k F j ↔ j = i := by
  classical
  let layerOf : Fin k → Fin k := fun i =>
    Classical.choose ((mem_layerUnion (canonicalLayers k F) (f i)).mp
      (canonicalLayers_cover_of_isKSperner hsp (hmem i)))
  have hlayerOf_mem (i : Fin k) :
      f i ∈ canonicalLayers k F (layerOf i) :=
    Classical.choose_spec ((mem_layerUnion (canonicalLayers k F) (f i)).mp
      (canonicalLayers_cover_of_isKSperner hsp (hmem i)))
  have hlayerOf_strict : StrictMono layerOf := by
    intro i j hij
    exact canonicalLayer_index_lt_of_ssubset F
      (hlayerOf_mem i) (hlayerOf_mem j) (hstrict hij)
  have hlayerOf_eq : layerOf = id := hlayerOf_strict.eq_id
  intro i j
  constructor
  · intro hij
    have hji : j = layerOf i := layer_index_unique
      (canonicalLayers_pairwiseDisjoint k F) hij (hlayerOf_mem i)
    simpa [hlayerOf_eq] using hji
  · intro hji
    subst j
    simpa [hlayerOf_eq] using hlayerOf_mem i

theorem strictChainList_uses_each_canonical_layer
    {k : Nat} {F : Family α}
    (hsp : IsKSperner k F)
    {c : List (Finset α)}
    (hc : IsStrictChainIn F c)
    (hlen : c.length = k) :
    ∀ i j : Fin k,
      c.get (Fin.cast hlen.symm i) ∈
        canonicalLayers k F j ↔ j = i := by
  let f : Fin k → Finset α := fun i => c.get (Fin.cast hlen.symm i)
  have hmem : ∀ i, f i ∈ F := by
    intro i
    exact IsStrictChainIn.get_mem hc (Fin.cast hlen.symm i)
  have hstrict : StrictMono f := by
    intro i j hij
    apply IsStrictChainIn.get_ssubset_get_of_lt hc
    simpa using (Fin.cast_lt_cast hlen.symm).mpr hij
  exact strictChain_uses_each_canonical_layer hsp f hmem hstrict

@[simp] theorem minimalMembers_empty :
    minimalMembers (∅ : Family α) = ∅ := by
  simp [minimalMembers]

@[simp] theorem canonicalRemainder_empty (i : Nat) :
    canonicalRemainder (∅ : Family α) i = ∅ := by
  induction i with
  | zero => rfl
  | succ i ih => simp [canonicalRemainder_succ, ih]

@[simp] theorem canonicalLayer_empty (i : Nat) :
    canonicalLayer (∅ : Family α) i = ∅ := by
  simp [canonicalLayer]

@[simp] theorem minimalMembers_singleton (S : Finset α) :
    minimalMembers ({S} : Family α) = {S} := by
  ext T
  rw [mem_minimalMembers]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨rfl, hminimal⟩
    rfl
  · intro hTS
    subst T
    refine ⟨rfl, ?_⟩
    intro U hU hUS
    have hEq : U = S := by simpa using hU
    subst U
    exact (lt_irrefl S) hUS

@[simp] theorem canonicalRemainder_singleton_succ
    (S : Finset α) (i : Nat) :
    canonicalRemainder ({S} : Family α) (i + 1) = ∅ := by
  have hsub : canonicalRemainder ({S} : Family α) (i + 1) ⊆
      canonicalRemainder ({S} : Family α) 1 :=
    canonicalRemainder_antitone _ (by omega)
  have hzero : canonicalRemainder ({S} : Family α) 1 = ∅ := by
    change ({S} : Family α) \ minimalMembers ({S} : Family α) = ∅
    rw [minimalMembers_singleton]
    simp
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨T, hT⟩
  have := hsub hT
  rw [hzero] at this
  simpa using this

theorem canonicalLayer_eq_empty_iff_remainder_eq_empty
    (F : Family α) (i : Nat) :
    canonicalLayer F i = ∅ ↔ canonicalRemainder F i = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  exact not_congr (minimalMembers_nonempty_iff _)

theorem canonicalLayer_empty_propagates
    (F : Family α) {i j : Nat} (hij : i ≤ j)
    (hi : canonicalLayer F i = ∅) :
    canonicalLayer F j = ∅ := by
  have hremi := (canonicalLayer_eq_empty_iff_remainder_eq_empty F i).mp hi
  apply (canonicalLayer_eq_empty_iff_remainder_eq_empty F j).mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨S, hS⟩
  have hSi := canonicalRemainder_antitone F hij hS
  simpa [hremi] using hSi

@[simp] theorem layerUnion_canonicalLayers_zero (F : Family α) :
    LayerUnion (canonicalLayers 0 F) = ∅ := by
  ext S
  simp

end AiMathLab.SaturatedSperner
