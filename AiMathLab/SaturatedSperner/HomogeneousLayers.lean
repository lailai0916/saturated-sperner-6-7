import AiMathLab.SaturatedSperner.HomogeneousAtom
import AiMathLab.SaturatedSperner.CanonicalDecomposition

/-!
# Homogeneous small and large layers

This module formalizes the common-atom small-layer criterion and the
homogeneous partial converse for canonical layers.  One explicit atom `H` is
shared by all layers in the criterion.
-/

universe u

namespace AiMathLab.SaturatedSperner

variable {α : Type u} [DecidableEq α]

/-- Members of `F` disjoint from the atom. -/
def SmallPart (F : Family α) (H : Finset α) : Family α :=
  F.filter fun S => Disjoint S H

/-- Members of `F` containing the atom. -/
def LargePart (F : Family α) (H : Finset α) : Family α :=
  F.filter fun S => H ⊆ S

/-- The paper's auxiliary set, containing exactly one selected atom point. -/
def partialAtomSet (S H : Finset α) (x : α) : Finset α :=
  (S \ H) ∪ {x}

@[simp] theorem mem_smallPart
    {F : Family α} {H S : Finset α} :
    S ∈ SmallPart F H ↔ S ∈ F ∧ Disjoint S H := by
  simp [SmallPart]

@[simp] theorem mem_largePart
    {F : Family α} {H S : Finset α} :
    S ∈ LargePart F H ↔ S ∈ F ∧ H ⊆ S := by
  simp [LargePart]

theorem smallPart_subset (F : Family α) (H : Finset α) :
    SmallPart F H ⊆ F := by
  intro S hS
  exact (mem_smallPart.mp hS).1

theorem largePart_subset (F : Family α) (H : Finset α) :
    LargePart F H ⊆ F := by
  intro S hS
  exact (mem_largePart.mp hS).1

theorem atomBlock_small_large_cover
    {F : Family α} {H : Finset α}
    (hblock : IsAtomBlock F H) :
    SmallPart F H ∪ LargePart F H = F := by
  ext S
  constructor
  · intro hS
    simp only [Finset.mem_union, mem_smallPart, mem_largePart] at hS
    exact hS.elim And.left And.left
  · intro hSF
    rcases hblock S hSF with hsmall | hlarge
    · exact Finset.mem_union_left _ (mem_smallPart.mpr ⟨hSF, hsmall⟩)
    · exact Finset.mem_union_right _ (mem_largePart.mpr ⟨hSF, hlarge⟩)

theorem smallPart_largePart_disjoint
    {F : Family α} {H : Finset α}
    (hHne : H.Nonempty) :
    Disjoint (SmallPart F H) (LargePart F H) := by
  rw [Finset.disjoint_left]
  intro S hsmall hlarge
  rcases hHne with ⟨x, hxH⟩
  have hxS := (mem_largePart.mp hlarge).2 hxH
  exact (Finset.disjoint_left.mp (mem_smallPart.mp hsmall).2) hxS hxH

theorem isSaturatedAntichain_of_external_comparable
    {F : Family α}
    (hanti : IsAntichain F)
    (hcomp : ∀ S : Finset α, S ∉ F →
      ∃ U : Finset α, U ∈ F ∧ (U ⊂ S ∨ S ⊂ U)) :
    IsSaturatedAntichain F := by
  refine ⟨hanti, ?_⟩
  intro S hSF
  rcases hcomp S hSF with ⟨U, hUF, hUS | hSU⟩
  · exact ⟨S, Finset.mem_insert_self S F,
      U, Finset.mem_insert_of_mem hUF, hUS⟩
  · exact ⟨U, Finset.mem_insert_of_mem hUF,
      S, Finset.mem_insert_self S F, hSU⟩

@[simp] theorem partialAtomSet_inter_atom
    {S H : Finset α} {x : α} (hx : x ∈ H) :
    partialAtomSet S H x ∩ H = {x} := by
  ext z
  simp [partialAtomSet, hx]

theorem partialAtomSet_not_disjoint
    {S H : Finset α} {x : α} (hx : x ∈ H) :
    ¬ Disjoint (partialAtomSet S H x) H := by
  intro hdisj
  exact (Finset.disjoint_left.mp hdisj)
    (by simp [partialAtomSet]) hx

theorem partialAtomSet_not_superset
    {S H : Finset α} {x y : α}
    (hy : y ∈ H) (hyx : y ≠ x) :
    ¬ H ⊆ partialAtomSet S H x := by
  intro hsub
  have hyT := hsub hy
  simpa [partialAtomSet, hy, hyx] using hyT

theorem partialAtomSet_not_mem_of_atomBlock
    {F : Family α} {S H : Finset α} {x y : α}
    (hblock : IsAtomBlock F H)
    (hx : x ∈ H) (hy : y ∈ H) (hyx : y ≠ x) :
    partialAtomSet S H x ∉ F := by
  intro hmem
  rcases hblock _ hmem with hdisj | hsub
  · exact partialAtomSet_not_disjoint hx hdisj
  · exact partialAtomSet_not_superset hy hyx hsub

theorem subset_original_of_disjoint_of_subset_partialAtomSet
    {S H U : Finset α} {x : α}
    (hx : x ∈ H)
    (hUH : Disjoint U H)
    (hUT : U ⊆ partialAtomSet S H x) :
    U ⊆ S := by
  intro z hzU
  have hzT := hUT hzU
  rw [partialAtomSet, Finset.mem_union] at hzT
  rcases hzT with hzDiff | hzx
  · exact (Finset.mem_sdiff.mp hzDiff).1
  · have hzx' : z = x := by simpa using hzx
    subst z
    exact False.elim ((Finset.disjoint_left.mp hUH) hzU hx)

theorem original_subset_of_atom_subset_of_partialAtomSet_subset
    {S H U : Finset α} {x : α}
    (hHU : H ⊆ U)
    (hTU : partialAtomSet S H x ⊆ U) :
    S ⊆ U := by
  intro z hzS
  by_cases hzH : z ∈ H
  · exact hHU hzH
  · apply hTU
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzS, hzH⟩)

theorem saturatedAntichain_small_or_large_comparable
    {F : Family α} {H S : Finset α}
    (hsat : IsSaturatedAntichain F)
    (hH : IsHomogeneousAtom F H)
    (hSF : S ∉ F) :
    (∃ A : Finset α, A ∈ SmallPart F H ∧ A ⊂ S) ∨
      (∃ B : Finset α, B ∈ LargePart F H ∧ S ⊂ B) := by
  have hHcard : 2 < H.card := hH.2
  have hcard : 1 < H.card := by omega
  rcases Finset.one_lt_card.mp hcard with ⟨x, hxH, y, hyH, hxy⟩
  have hyx : y ≠ x := hxy.symm
  let T := partialAtomSet S H x
  have hTF : T ∉ F := partialAtomSet_not_mem_of_atomBlock
    hH.1.1 hxH hyH hyx
  rcases exists_comparable_of_isSaturatedAntichain hsat hTF with
    ⟨U, hUF, hUT | hTU⟩
  · rcases hH.1.1 U hUF with hUdisj | hUlarge
    · left
      refine ⟨U, mem_smallPart.mpr ⟨hUF, hUdisj⟩, ?_⟩
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨subset_original_of_disjoint_of_subset_partialAtomSet
        hxH hUdisj hUT.1, ?_⟩
      intro hEq
      subst U
      exact hSF hUF
    · exact False.elim
        (partialAtomSet_not_superset hyH hyx (hUlarge.trans hUT.1))
  · rcases hH.1.1 U hUF with hUdisj | hUlarge
    · have hxU : x ∈ U := hTU.1 (by simp [T, partialAtomSet])
      exact False.elim ((Finset.disjoint_left.mp hUdisj) hxU hxH)
    · right
      refine ⟨U, mem_largePart.mpr ⟨hUF, hUlarge⟩, ?_⟩
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨original_subset_of_atom_subset_of_partialAtomSet_subset
        hUlarge hTU.1, ?_⟩
      intro hEq
      subst U
      exact hSF hUF

theorem smallParts_layered_iff
    {k : Nat} (A : Fin k → Family α) (H : Finset α)
    (hsat : ∀ i, IsSaturatedAntichain (A i))
    (hdisj : PairwiseDisjointLayers A)
    (hH : ∀ i, IsHomogeneousAtom (A i) H) :
    IsLayered (fun i => SmallPart (A i) H) ↔ IsLayered A := by
  constructor
  · intro hsmall
    intro i hi D hD
    let lo : Fin k := ⟨i, by omega⟩
    let up : Fin k := ⟨i + 1, hi⟩
    have hlone : lo ≠ up := by
      intro h
      simp [lo, up] at h
    have hDnotlo : D ∉ A lo := by
      intro hDlo
      exact Finset.disjoint_left.mp (hdisj hlone) hDlo hD
    rcases saturatedAntichain_small_or_large_comparable
        (hsat lo) (hH lo) hDnotlo with
      ⟨C, hCsmall, hCD⟩ | ⟨C, hClarge, hDC⟩
    · exact ⟨C, smallPart_subset _ _ hCsmall, hCD⟩
    · have hClo : C ∈ A lo := largePart_subset _ _ hClarge
      have hCnotup : C ∉ A up := by
        intro hCup
        exact Finset.disjoint_left.mp (hdisj hlone) hClo hCup
      rcases saturatedAntichain_small_or_large_comparable
          (hsat up) (hH up) hCnotup with
        ⟨E, hEsmall, hEC⟩ | ⟨E, hElarge, hCE⟩
      · rcases hsmall i hi E hEsmall with ⟨B, hBsmall, hBE⟩
        have hBlo : B ∈ A lo := smallPart_subset _ _ hBsmall
        have hBC : B ⊂ C := strictSubset_trans hBE hEC
        exact False.elim
          (IsAntichain.not_ssubset (hsat lo).1 hBlo hClo hBC)
      · have hEup : E ∈ A up := largePart_subset _ _ hElarge
        have hDE : D ⊂ E := strictSubset_trans hDC hCE
        exact False.elim
          (IsAntichain.not_ssubset (hsat up).1 hD hEup hDE)
  · intro hwhole
    intro i hi D hDsmall
    rcases hwhole i hi D (smallPart_subset _ _ hDsmall) with ⟨C, hC, hCD⟩
    have hDdisj := (mem_smallPart.mp hDsmall).2
    have hCdisj : Disjoint C H := by
      rw [Finset.disjoint_left]
      intro x hxC hxH
      exact (Finset.disjoint_left.mp hDdisj) (hCD.1 hxC) hxH
    exact ⟨C, mem_smallPart.mpr ⟨hC, hCdisj⟩, hCD⟩

/-- Removing the inserted set from a true through-chain leaves exactly the
`k` original-family members, still strictly ordered and each comparable with
the removed set. -/
theorem erase_inserted_of_strictChainWitness
    {k : Nat} {F : Family α} {T : Finset α}
    {c : List (Finset α)}
    (hTF : T ∉ F)
    (hc : IsStrictChainWitness (k + 1) (insert T F) T c) :
    (c.erase T).length = k ∧
      IsStrictChainIn F (c.erase T) ∧
      (∀ U, U ∈ c.erase T ↔ U ∈ c ∧ U ≠ T) ∧
      ∀ U, U ∈ c.erase T → (U ⊂ T ∨ T ⊂ U) := by
  have hpair : c.Pairwise (· ⊂ ·) :=
    IsStrictChainIn.pairwise_ssubset hc.2.1
  have hnodup : c.Nodup := List.nodup_iff_pairwise_ne.mpr
    (hpair.imp (fun hAB hEq => by subst hEq; exact (lt_irrefl _) hAB))
  have hlengthErase := List.length_erase_add_one hc.2.2
  have hlengthChain : c.length = k + 1 := hc.1
  have hlen : (c.erase T).length = k := by omega
  have hmemErase (U : Finset α) :
      U ∈ c.erase T ↔ U ∈ c ∧ U ≠ T := by
    rw [hnodup.mem_erase_iff]
    tauto
  have hchainErase : IsStrictChainIn F (c.erase T) := by
    rw [isStrictChainIn_iff_forall_mem_and_isChain]
    constructor
    · intro U hU
      have hUc := (hmemErase U).mp hU |>.1
      have hUne := (hmemErase U).mp hU |>.2
      have hUinsert :=
        (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hc.2.1 |>.1 U hUc
      simpa [hUne] using hUinsert
    · exact (hpair.erase T).isChain
  refine ⟨hlen, hchainErase, hmemErase, ?_⟩
  intro U hU
  have hUc := (hmemErase U).mp hU |>.1
  have hUne := (hmemErase U).mp hU |>.2
  rcases List.mem_iff_get.mp hUc with ⟨iu, hiu⟩
  rcases List.mem_iff_get.mp hc.2.2 with ⟨it, hit⟩
  have hiune : iu ≠ it := by
    intro hEq
    subst it
    apply hUne
    rw [← hiu, ← hit]
  rcases Fin.lt_or_lt_of_ne hiune with huit | htiu
  · left
    have hrel := hpair.rel_get_of_lt huit
    rw [hiu, hit] at hrel
    exact hrel
  · right
    have hrel := hpair.rel_get_of_lt htiu
    rw [hit, hiu] at hrel
    exact hrel

theorem canonicalLayers_saturated_of_homogeneousAtom
    {k : Nat} (hk : 0 < k)
    (F : Family α) (H : Finset α)
    (hsat : IsSaturatedKSperner k F)
    (hH : IsHomogeneousAtom F H) :
    ∀ i : Fin k,
      IsSaturatedAntichain (canonicalLayers k F i) := by
  intro i
  apply isSaturatedAntichain_of_external_comparable
    (canonicalLayers_antichain k F i)
  intro S hSlayer
  have hHcard : 2 < H.card := hH.2
  have hcard : 1 < H.card := by omega
  rcases Finset.one_lt_card.mp hcard with ⟨x, hxH, y, hyH, hxy⟩
  have hyx : y ≠ x := hxy.symm
  let T := partialAtomSet S H x
  have hTF : T ∉ F := partialAtomSet_not_mem_of_atomBlock
    hH.1.1 hxH hyH hyx
  have hthrough :=
    (isSaturatedKSperner_iff_hasStrictChainThrough k F).mp hsat |>.2 T hTF
  rcases hthrough with ⟨c, hc⟩
  rcases erase_inserted_of_strictChainWitness hTF hc with
    ⟨hlen, hchain, hmemErase, hcomparable⟩
  let d := c.erase T
  let idx : Fin d.length := Fin.cast hlen.symm i
  let U := d.get idx
  have hUd : U ∈ d := List.get_mem d idx
  have hUlayer : U ∈ canonicalLayers k F i := by
    have halign := strictChainList_uses_each_canonical_layer
      hsat.1 hchain hlen i i
    exact halign.mpr rfl
  have hUF : U ∈ F := IsStrictChainIn.get_mem hchain idx
  rcases hcomparable U hUd with hUT | hTU
  · rcases hH.1.1 U hUF with hUdisj | hUlarge
    · refine ⟨U, hUlayer, Or.inl ?_⟩
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨subset_original_of_disjoint_of_subset_partialAtomSet
        hxH hUdisj hUT.1, ?_⟩
      intro hEq
      apply hSlayer
      rw [← hEq]
      exact hUlayer
    · exact False.elim
        (partialAtomSet_not_superset hyH hyx (hUlarge.trans hUT.1))
  · rcases hH.1.1 U hUF with hUdisj | hUlarge
    · have hxU : x ∈ U := hTU.1 (by simp [T, partialAtomSet])
      exact False.elim ((Finset.disjoint_left.mp hUdisj) hxU hxH)
    · refine ⟨U, hUlayer, Or.inr ?_⟩
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨original_subset_of_atom_subset_of_partialAtomSet_subset
        hUlarge hTU.1, ?_⟩
      intro hEq
      apply hSlayer
      rw [hEq]
      exact hUlayer

theorem canonicalLayers_saturated_of_homogeneousAtom_finiteGround
    [Fintype α]
    {k : Nat} (hk : 0 < k)
    (F : Family α) (H : Finset α)
    (hsat : IsSaturatedKSperner k F)
    (hH : IsHomogeneousAtom F H) :
    ∀ i : Fin k,
      IsSaturatedAntichain (canonicalLayers k F i) :=
  canonicalLayers_saturated_of_homogeneousAtom hk F H hsat hH

end AiMathLab.SaturatedSperner
