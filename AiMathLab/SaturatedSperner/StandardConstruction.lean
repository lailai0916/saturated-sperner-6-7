import AiMathLab.SaturatedSperner.Composition
import AiMathLab.SaturatedSperner.Layered

/-!
# The symbolic standard construction

This module formalizes the standard saturated family used to fill the
remainder of the ground set in the eventual P0053 upper bound.  Its layers
are indexed by compressed rank: a small member with core rank `i` and a large
member with core rank `i - 1` occupy the same layer.

All arguments are symbolic in `s` and in the atom type `H`; no fixed finite
enumeration is used.
-/

universe u

namespace AiMathLab.SaturatedSperner

/-- Small members of the standard family: an arbitrary core and no atom
points. -/
def standardSmall
    (s : Nat) (H : Type u) [Fintype H] [DecidableEq H] :
    Family (Fin s ⊕ H) :=
  Finset.univ.image fun C : Finset (Fin s) =>
    sumSubset C ∅

/-- Large members of the standard family: an arbitrary core and the whole
atom. -/
def standardLarge
    (s : Nat) (H : Type u) [Fintype H] [DecidableEq H] :
    Family (Fin s ⊕ H) :=
  Finset.univ.image fun C : Finset (Fin s) =>
    sumSubset C Finset.univ

/-- The two-part standard family. -/
def standardFamily
    (s : Nat) (H : Type u) [Fintype H] [DecidableEq H] :
    Family (Fin s ⊕ H) :=
  standardSmall s H ∪ standardLarge s H

/-- The right summand is the distinguished standard atom. -/
def standardAtom
    (s : Nat) (H : Type u) [Fintype H] [DecidableEq H] :
    Finset (Fin s ⊕ H) :=
  sumSubset ∅ Finset.univ

/-- Compressed-rank layer `i`: small core rank `i`, or large core rank
`i - 1`. -/
def standardLayer
    (s : Nat) (H : Type u) [Fintype H] [DecidableEq H]
    (i : Fin (s + 2)) : Family (Fin s ⊕ H) :=
  ((Finset.univ.filter fun C : Finset (Fin s) =>
      C.card = i.val).image fun C => sumSubset C ∅) ∪
    ((Finset.univ.filter fun C : Finset (Fin s) =>
      C.card + 1 = i.val).image fun C =>
        sumSubset C Finset.univ)

section Standard

variable {s : Nat} {H : Type u} [Fintype H] [DecidableEq H]

@[simp] theorem mem_standardSmall_iff
    {S : Finset (Fin s ⊕ H)} :
    S ∈ standardSmall s H ↔ rightProjection S = ∅ := by
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨C, -, hCS⟩
    simpa using (congrArg rightProjection hCS).symm
  · intro hright
    refine Finset.mem_image.mpr ⟨leftProjection S, Finset.mem_univ _, ?_⟩
    simpa [hright] using sumSubset_projections S

@[simp] theorem mem_standardLarge_iff
    {S : Finset (Fin s ⊕ H)} :
    S ∈ standardLarge s H ↔ rightProjection S = Finset.univ := by
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨C, -, hCS⟩
    simpa using (congrArg rightProjection hCS).symm
  · intro hright
    refine Finset.mem_image.mpr ⟨leftProjection S, Finset.mem_univ _, ?_⟩
    simpa [hright] using sumSubset_projections S

@[simp] theorem mem_standardFamily_iff
    {S : Finset (Fin s ⊕ H)} :
    S ∈ standardFamily s H ↔
      rightProjection S = ∅ ∨ rightProjection S = Finset.univ := by
  simp [standardFamily]

@[simp] theorem mem_standardLayer_iff
    {i : Fin (s + 2)} {S : Finset (Fin s ⊕ H)} :
    S ∈ standardLayer s H i ↔
      (rightProjection S = ∅ ∧ (leftProjection S).card = i.val) ∨
      (rightProjection S = Finset.univ ∧
        (leftProjection S).card + 1 = i.val) := by
  constructor
  · intro hS
    rw [standardLayer, Finset.mem_union] at hS
    rcases hS with hsmall | hlarge
    · rcases Finset.mem_image.mp hsmall with ⟨C, hC, rfl⟩
      left
      simpa using (Finset.mem_filter.mp hC).2
    · rcases Finset.mem_image.mp hlarge with ⟨C, hC, rfl⟩
      right
      simpa using (Finset.mem_filter.mp hC).2
  · rintro (⟨hright, hcard⟩ | ⟨hright, hcard⟩)
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr
        ⟨leftProjection S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩, ?_⟩
      simpa [hright] using sumSubset_projections S
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr
        ⟨leftProjection S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩, ?_⟩
      simpa [hright] using sumSubset_projections S

private theorem standardLayer_not_ssubset
    (hH : 0 < Fintype.card H) (i : Fin (s + 2))
    {A B : Finset (Fin s ⊕ H)}
    (hA : A ∈ standardLayer s H i)
    (hB : B ∈ standardLayer s H i) :
    ¬ A ⊂ B := by
  intro hAB
  rcases mem_standardLayer_iff.mp hA with
      ⟨hAr, hAc⟩ | ⟨hAr, hAc⟩ <;>
    rcases mem_standardLayer_iff.mp hB with
      ⟨hBr, hBc⟩ | ⟨hBr, hBc⟩
  · rcases projections_ssubset_control hAB with hleft | hright
    · have := Finset.card_lt_card hleft.1
      omega
    · rw [hAr, hBr] at hright
      exact (lt_irrefl _ hright.2).elim
  · have hleft := leftProjection_mono hAB.le
    have hcard := Finset.card_le_card hleft
    omega
  · have hright := rightProjection_mono hAB.le
    rw [hAr, hBr] at hright
    letI : Nonempty H := Fintype.card_pos_iff.mp hH
    rcases Finset.univ_nonempty (α := H) with ⟨x, hx⟩
    exact (by simpa using hright hx)
  · rcases projections_ssubset_control hAB with hleft | hright
    · have := Finset.card_lt_card hleft.1
      omega
    · rw [hAr, hBr] at hright
      exact (lt_irrefl _ hright.2).elim

private theorem standardLayer_antichain
    (hH : 0 < Fintype.card H) (i : Fin (s + 2)) :
    IsAntichain (standardLayer s H i) := by
  intro hchain
  rcases hchain with ⟨B, hB, A, hA, hAB⟩
  exact standardLayer_not_ssubset hH i hA hB hAB

/-- Every compressed-rank layer is a saturated antichain. -/
theorem standardLayer_saturatedAntichain
    (hH : 0 < Fintype.card H) (i : Fin (s + 2)) :
    IsSaturatedKSperner 1 (standardLayer s H i) := by
  apply isSaturatedAntichain_of_external_comparable
    (standardLayer_antichain hH i)
  intro S hS
  by_cases hlo : i.val ≤ (leftProjection S).card
  · rcases Finset.exists_subset_card_eq hlo with ⟨D, hDsub, hDcard⟩
    let U : Finset (Fin s ⊕ H) := sumSubset D ∅
    have hUmem : U ∈ standardLayer s H i := by
      apply mem_standardLayer_iff.mpr
      left
      simp [U, hDcard]
    refine ⟨U, hUmem, Or.inl ?_⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨sumSubset_subset_arbitrary_iff.mpr ⟨hDsub, by simp⟩, ?_⟩
    intro hEq
    exact hS (hEq ▸ hUmem)
  · have hcorelt : (leftProjection S).card < i.val := by omega
    have hiPos : 0 < i.val := by omega
    have htargetCore : (leftProjection S).card ≤ i.val - 1 := by omega
    have htargetGround : i.val - 1 ≤ Fintype.card (Fin s) := by
      simp only [Fintype.card_fin]
      omega
    rcases Finset.exists_superset_card_eq htargetCore htargetGround with
      ⟨E, hEsub, hEcard⟩
    let U : Finset (Fin s ⊕ H) := sumSubset E Finset.univ
    have hUmem : U ∈ standardLayer s H i := by
      apply mem_standardLayer_iff.mpr
      right
      constructor
      · simp [U]
      · simp only [U, leftProjection_sumSubset]
        omega
    refine ⟨U, hUmem, Or.inr ?_⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨arbitrary_subset_sumSubset_iff.mpr
      ⟨hEsub, Finset.subset_univ _⟩, ?_⟩
    intro hEq
    exact hS (hEq.symm ▸ hUmem)

/-- The compressed-rank layers cover exactly the two-part standard family. -/
theorem standard_layerUnion
    (hH : 0 < Fintype.card H) :
    LayerUnion (standardLayer s H) = standardFamily s H := by
  ext S
  constructor
  · intro hS
    rcases (mem_layerUnion (standardLayer s H) S).mp hS with ⟨i, hi⟩
    rcases mem_standardLayer_iff.mp hi with hsmall | hlarge
    · exact mem_standardFamily_iff.mpr (Or.inl hsmall.1)
    · exact mem_standardFamily_iff.mpr (Or.inr hlarge.1)
  · intro hS
    have hcore : (leftProjection S).card ≤ s := by
      simpa only [Fintype.card_fin] using
        (leftProjection S).card_le_univ
    rcases mem_standardFamily_iff.mp hS with hsmall | hlarge
    · let i : Fin (s + 2) :=
        ⟨(leftProjection S).card, by omega⟩
      apply (mem_layerUnion (standardLayer s H) S).mpr
      refine ⟨i, mem_standardLayer_iff.mpr (Or.inl ?_)⟩
      exact ⟨hsmall, rfl⟩
    · let i : Fin (s + 2) :=
        ⟨(leftProjection S).card + 1, by omega⟩
      apply (mem_layerUnion (standardLayer s H) S).mpr
      refine ⟨i, mem_standardLayer_iff.mpr (Or.inr ?_)⟩
      exact ⟨hlarge, rfl⟩

/-- Different compressed-rank layers are disjoint. -/
theorem standardLayers_pairwiseDisjoint
    (hH : 0 < Fintype.card H) :
    PairwiseDisjointLayers (standardLayer s H) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro S hSi hSj
  rcases mem_standardLayer_iff.mp hSi with
      ⟨hSir, hSic⟩ | ⟨hSir, hSic⟩ <;>
    rcases mem_standardLayer_iff.mp hSj with
      ⟨hSjr, hSjc⟩ | ⟨hSjr, hSjc⟩
  · apply hij
    apply Fin.ext
    omega
  · have hemptyUniv : (∅ : Finset H) = Finset.univ :=
      hSir.symm.trans hSjr
    letI : Nonempty H := Fintype.card_pos_iff.mp hH
    rcases Finset.univ_nonempty (α := H) with ⟨x, hx⟩
    have : x ∈ (∅ : Finset H) := by rw [hemptyUniv]; exact hx
    simpa using this
  · have hunivEmpty : (Finset.univ : Finset H) = ∅ :=
      hSir.symm.trans hSjr
    letI : Nonempty H := Fintype.card_pos_iff.mp hH
    rcases Finset.univ_nonempty (α := H) with ⟨x, hx⟩
    have : x ∈ (∅ : Finset H) := by rw [← hunivEmpty]; exact hx
    simpa using this
  · apply hij
    apply Fin.ext
    omega

/-- Each member in layer `i + 1` has a strict predecessor in layer `i`.
The proof keeps the small and large source branches separate. -/
theorem standardLayers_layered
    (hH : 0 < Fintype.card H) :
    IsLayered (standardLayer s H) := by
  intro i hi D hD
  rcases mem_standardLayer_iff.mp hD with
      ⟨hDright, hDcard⟩ | ⟨hDright, hDcard⟩
  · have hcorePos : 0 < (leftProjection D).card := by
      change (leftProjection D).card = i + 1 at hDcard
      omega
    rcases Finset.card_pos.mp hcorePos with ⟨x, hx⟩
    let C := leftProjection D
    let P : Finset (Fin s ⊕ H) := sumSubset (C.erase x) ∅
    have hPmem : P ∈ standardLayer s H ⟨i, by omega⟩ := by
      apply mem_standardLayer_iff.mpr
      left
      constructor
      · simp [P]
      · simp only [P, leftProjection_sumSubset]
        have hxC : x ∈ C := hx
        rw [Finset.card_erase_of_mem hxC]
        change C.card = i + 1 at hDcard
        omega
    refine ⟨P, hPmem, ?_⟩
    rw [← sumSubset_projections D, hDright]
    apply sumSubset_ssubset_control.mpr
    left
    exact ⟨Finset.erase_ssubset hx, Finset.Subset.rfl⟩
  · let C := leftProjection D
    let P : Finset (Fin s ⊕ H) := sumSubset C ∅
    have hPmem : P ∈ standardLayer s H ⟨i, by omega⟩ := by
      apply mem_standardLayer_iff.mpr
      left
      constructor
      · simp [P]
      · simp only [P, leftProjection_sumSubset]
        change C.card + 1 = i + 1 at hDcard
        omega
    refine ⟨P, hPmem, ?_⟩
    letI : Nonempty H := Fintype.card_pos_iff.mp hH
    have hempty : (∅ : Finset H) ⊂ Finset.univ :=
      (Finset.univ_nonempty (α := H)).empty_ssubset
    rw [← sumSubset_projections D, hDright]
    apply sumSubset_ssubset_control.mpr
    right
    exact ⟨Finset.Subset.rfl, hempty⟩

/-- The symbolic standard family is saturated `(s + 2)`-Sperner. -/
theorem standard_saturated
    (hH : 2 < Fintype.card H) :
    IsSaturatedKSperner (s + 2) (standardFamily s H) := by
  have hHpos : 0 < Fintype.card H := by omega
  have hsaturated := layered_saturated_antichains
    (α := Fin s ⊕ H) (k := s + 2) (by omega)
    (standardLayer s H)
    (standardLayer_saturatedAntichain hHpos)
    (standardLayers_pairwiseDisjoint hHpos)
    (standardLayers_layered hHpos)
  rw [standard_layerUnion hHpos] at hsaturated
  exact hsaturated

/-- Both Boolean-lattice endpoints occur in the standard family. -/
theorem standard_hasEndpoints
    (hH : 2 < Fintype.card H) :
    HasEndpoints (standardFamily s H) := by
  constructor
  · apply mem_standardFamily_iff.mpr
    left
    simp
  · apply mem_standardFamily_iff.mpr
    right
    simp

private theorem standard_atomBlock :
    IsAtomBlock (standardFamily s H) (standardAtom s H) := by
  intro S hS
  rcases mem_standardFamily_iff.mp hS with hsmall | hlarge
  · left
    rw [Finset.disjoint_left]
    intro z hzS hzAtom
    cases z with
    | inl a => simpa [standardAtom] using hzAtom
    | inr b =>
        have hb : b ∈ rightProjection S := by
          simpa [rightProjection] using hzS
        rw [hsmall] at hb
        simpa using hb
  · right
    apply sumSubset_subset_arbitrary_iff.mpr
    exact ⟨by simp [standardAtom], by simpa [standardAtom, hlarge]⟩

/-- The right summand is a homogeneous atom of the standard family. -/
theorem standard_homogeneousAtom
    (hH : 2 < Fintype.card H) :
    IsHomogeneousAtom (standardFamily s H) (standardAtom s H) := by
  refine ⟨⟨standard_atomBlock, ?_⟩, ?_⟩
  · intro K hAtomK hKblock
    have hnotSubset : ¬ K ⊆ standardAtom s H := by
      intro hKsub
      exact hAtomK.ne (Finset.Subset.antisymm hAtomK.le hKsub)
    rcases Finset.sdiff_nonempty.mpr hnotSubset with ⟨z, hz⟩
    have hzK : z ∈ K := (Finset.mem_sdiff.mp hz).1
    have hzNotAtom : z ∉ standardAtom s H := (Finset.mem_sdiff.mp hz).2
    cases z with
    | inr b =>
        exact hzNotAtom (by simp [standardAtom])
    | inl a =>
        let A : Finset (Fin s ⊕ H) := sumSubset {a} ∅
        have hAF : A ∈ standardFamily s H := by
          apply mem_standardFamily_iff.mpr
          left
          simp [A]
        rcases hKblock A hAF with hdisj | hKsub
        · exact (Finset.disjoint_left.mp hdisj)
            (by simp [A]) hzK
        · letI : Nonempty H := Fintype.card_pos_iff.mp (by omega)
          rcases Finset.univ_nonempty (α := H) with ⟨y, hy⟩
          have hyAtom : Sum.inr y ∈ standardAtom s H := by
            simp [standardAtom]
          have hyK : Sum.inr y ∈ K := hAtomK.le hyAtom
          have hyA := hKsub hyK
          simpa [A] using hyA
  · simpa [standardAtom] using hH

/-- The homogeneous small part is exactly the explicitly defined small
image. -/
theorem standard_smallPart
    (hH : 2 < Fintype.card H) :
    SmallPart (standardFamily s H) (standardAtom s H) =
      standardSmall s H := by
  ext S
  constructor
  · intro hS
    rcases mem_smallPart.mp hS with ⟨hSF, hdisj⟩
    rcases mem_standardFamily_iff.mp hSF with hsmall | hlarge
    · exact mem_standardSmall_iff.mpr hsmall
    · letI : Nonempty H := Fintype.card_pos_iff.mp (by omega)
      rcases Finset.univ_nonempty (α := H) with ⟨y, hy⟩
      have hyS : Sum.inr y ∈ S := by
        have hyRight : y ∈ rightProjection S := by
          rw [hlarge]
          exact hy
        simpa [rightProjection] using hyRight
      have hyAtom : Sum.inr y ∈ standardAtom s H := by
        simp [standardAtom]
      exact False.elim ((Finset.disjoint_left.mp hdisj) hyS hyAtom)
  · intro hS
    have hright := mem_standardSmall_iff.mp hS
    apply mem_smallPart.mpr
    constructor
    · exact mem_standardFamily_iff.mpr (Or.inl hright)
    · rw [Finset.disjoint_left]
      intro z hzS hzAtom
      cases z with
      | inl a => simpa [standardAtom] using hzAtom
      | inr b =>
          have hb : b ∈ rightProjection S := by
            simpa [rightProjection] using hzS
          rw [hright] at hb
          simpa using hb

/-- The homogeneous large part is exactly the explicitly defined large
image. -/
theorem standard_largePart
    (hH : 2 < Fintype.card H) :
    LargePart (standardFamily s H) (standardAtom s H) =
      standardLarge s H := by
  ext S
  constructor
  · intro hS
    rcases mem_largePart.mp hS with ⟨hSF, hAtomSub⟩
    rcases mem_standardFamily_iff.mp hSF with hsmall | hlarge
    · letI : Nonempty H := Fintype.card_pos_iff.mp (by omega)
      rcases Finset.univ_nonempty (α := H) with ⟨y, hy⟩
      have hyAtom : Sum.inr y ∈ standardAtom s H := by
        simp [standardAtom]
      have hyS := hAtomSub hyAtom
      have hyRight : y ∈ rightProjection S := by
        simpa [rightProjection] using hyS
      rw [hsmall] at hyRight
      simpa using hyRight
    · exact mem_standardLarge_iff.mpr hlarge
  · intro hS
    have hright := mem_standardLarge_iff.mp hS
    apply mem_largePart.mpr
    constructor
    · exact mem_standardFamily_iff.mpr (Or.inr hright)
    · apply sumSubset_subset_arbitrary_iff.mpr
      exact ⟨by simp [standardAtom], by simpa [standardAtom, hright]⟩

private theorem standardSmall_card_raw :
    (standardSmall s H).card = 2 ^ s := by
  let f : Finset (Fin s) → Finset (Fin s ⊕ H) :=
    fun C => sumSubset C ∅
  have hf : Function.Injective f := by
    intro A B hAB
    simpa only [f, leftProjection_sumSubset] using
      congrArg leftProjection hAB
  calc
    (standardSmall s H).card =
        (Finset.univ : Finset (Finset (Fin s))).card := by
      simpa [standardSmall, f] using
        Finset.card_image_of_injective
          (Finset.univ : Finset (Finset (Fin s))) hf
    _ = 2 ^ s := by simp [Fintype.card_finset]

private theorem standardLarge_card_raw :
    (standardLarge s H).card = 2 ^ s := by
  let f : Finset (Fin s) → Finset (Fin s ⊕ H) :=
    fun C => sumSubset C Finset.univ
  have hf : Function.Injective f := by
    intro A B hAB
    simpa only [f, leftProjection_sumSubset] using
      congrArg leftProjection hAB
  calc
    (standardLarge s H).card =
        (Finset.univ : Finset (Finset (Fin s))).card := by
      simpa [standardLarge, f] using
        Finset.card_image_of_injective
          (Finset.univ : Finset (Finset (Fin s))) hf
    _ = 2 ^ s := by simp [Fintype.card_finset]

/-- The standard small part has exactly `2^s` members. -/
theorem standard_small_card
    (hH : 2 < Fintype.card H) :
    (SmallPart (standardFamily s H) (standardAtom s H)).card = 2 ^ s := by
  rw [standard_smallPart hH]
  exact standardSmall_card_raw

/-- The standard large part has exactly `2^s` members. -/
theorem standard_large_card
    (hH : 2 < Fintype.card H) :
    (LargePart (standardFamily s H) (standardAtom s H)).card = 2 ^ s := by
  rw [standard_largePart hH]
  exact standardLarge_card_raw

/-- The total standard family has exactly `2^(s+1)` members, derived from
the two disjoint atom parts. -/
theorem standard_card
    (hH : 2 < Fintype.card H) :
    (standardFamily s H).card = 2 ^ (s + 1) := by
  have hblock := (standard_homogeneousAtom (s := s) (H := H) hH).1.1
  have hcover := atomBlock_small_large_cover hblock
  have hHnonempty : (standardAtom s H).Nonempty := by
    have : 0 < (standardAtom s H).card := by
      simpa [standardAtom] using (show 0 < Fintype.card H by omega)
    exact Finset.card_pos.mp this
  calc
    (standardFamily s H).card =
        (SmallPart (standardFamily s H) (standardAtom s H) ∪
          LargePart (standardFamily s H) (standardAtom s H)).card := by
      rw [hcover]
    _ = (SmallPart (standardFamily s H) (standardAtom s H)).card +
        (LargePart (standardFamily s H) (standardAtom s H)).card :=
      Finset.card_union_of_disjoint
        (smallPart_largePart_disjoint hHnonempty)
    _ = 2 ^ s + 2 ^ s := by
      rw [standard_small_card hH, standard_large_card hH]
    _ = 2 ^ (s + 1) := by rw [pow_succ]; omega

/-- Public bundle for the standard construction. -/
theorem standard_full
    (hH : 2 < Fintype.card H) :
    IsSaturatedKSperner (s + 2) (standardFamily s H) ∧
      HasEndpoints (standardFamily s H) ∧
      IsHomogeneousAtom (standardFamily s H) (standardAtom s H) ∧
      SmallPart (standardFamily s H) (standardAtom s H) =
        standardSmall s H ∧
      LargePart (standardFamily s H) (standardAtom s H) =
        standardLarge s H ∧
      (SmallPart (standardFamily s H) (standardAtom s H)).card = 2 ^ s ∧
      (LargePart (standardFamily s H) (standardAtom s H)).card = 2 ^ s ∧
      (standardFamily s H).card = 2 ^ (s + 1) := by
  exact ⟨standard_saturated hH, standard_hasEndpoints hH,
    standard_homogeneousAtom hH, standard_smallPart hH,
    standard_largePart hH, standard_small_card hH,
    standard_large_card hH, standard_card hH⟩

end Standard

end AiMathLab.SaturatedSperner
