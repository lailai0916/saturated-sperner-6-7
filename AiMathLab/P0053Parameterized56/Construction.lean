import AiMathLab.P0053Parameterized56.CoreCertificate
import AiMathLab.SaturatedSperner.HomogeneousAtom

/-!
# The full parameterized 56-member construction

This module lifts the closed template facts through realization, proves the
embedded atom maximal, and applies the F3B layered saturated-antichain theorem.
It has no dependency on the frozen `Fin 10` F1 development.
-/

universe v

namespace AiMathLab.P0053Parameterized56

open AiMathLab.SaturatedSperner

/-- Realization injectivity lifts complete template-layer disjointness to the
seven realized layers. -/
theorem parameterized56_layers_pairwiseDisjoint
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    PairwiseDisjointLayers (parameterized56Layers H) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro D hDi hDj
  rcases Finset.mem_image.mp hDi with ⟨s, hs, hsD⟩
  rcases Finset.mem_image.mp hDj with ⟨t, ht, htD⟩
  have hst : s = t := realizeTemplate_injective hH (hsD.trans htD.symm)
  subst t
  exact Finset.disjoint_left.mp
    (templateLayers_pairwiseDisjoint hij) hs ht

/-- The realized layers satisfy F3B's source-direction layering condition. -/
theorem parameterized56_layers_layered
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    IsLayered (parameterized56Layers H) := by
  intro i hi D hD
  rcases Finset.mem_image.mp hD with ⟨t, ht, htD⟩
  let j : Fin 6 := ⟨i, by omega⟩
  have ht' : t ∈ templateLayer ⟨j.val + 1, by omega⟩ := by
    simpa [j] using ht
  rcases templateLayers_layered j t ht' with ⟨s, hs, hst⟩
  refine ⟨realizeTemplate H s, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨s, by simpa [j] using hs, rfl⟩
  · rw [← htD]
    exact (realizeTemplate_ssubset_realizeTemplate_iff hH s t).mpr hst

/-- Exact cardinality of the realized union. -/
theorem parameterized56_card
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    (parameterized56 H).card = 56 :=
  parameterized56_card_from_templates hH

/-- The small cycle edge through a core point; all seven such templates occur
in source layer two. -/
def cycleEdgeTemplate (i : Fin 7) : Template :=
  ⟨{i, ⟨(i.val + 1) % 7, Nat.mod_lt _ (by omega)⟩}, .small⟩

private def cycleEdgeMask : Fin 7 → Fin 128 :=
  ![3, 6, 12, 24, 48, 96, 65]

private theorem cycleEdgeTemplate_eq_smallMask (i : Fin 7) :
    cycleEdgeTemplate i = smallMask (cycleEdgeMask i) := by
  fin_cases i <;>
    apply (template_eq_iff _ _).mpr <;>
    constructor
  all_goals
    first
    | rfl
    | ext a
      fin_cases a <;>
        simp [cycleEdgeTemplate, cycleEdgeMask, smallMask, coreFromMask] <;>
        decide

theorem cycleEdgeTemplate_mem_layer2 (i : Fin 7) :
    cycleEdgeTemplate i ∈ templateLayer 2 := by
  rw [cycleEdgeTemplate_eq_smallMask]
  fin_cases i <;> simp [cycleEdgeMask, templateLayer, sourceRows]

@[simp] theorem self_mem_cycleEdgeTemplate_core (i : Fin 7) :
    i ∈ (cycleEdgeTemplate i).core := by
  simp [cycleEdgeTemplate]

/-- Every realized family member contains all or none of the embedded atom. -/
theorem parameterized56_atomBlock
    {H : Type v} [Fintype H] [DecidableEq H] :
    IsAtomBlock (parameterized56 H) (embeddedAtom H) := by
  intro S hS
  rw [parameterized56_eq_image_templateUnion] at hS
  rcases Finset.mem_image.mp hS with ⟨t, ht, hreal⟩
  subst S
  cases t with
  | mk C use =>
      cases use with
      | small =>
          left
          rw [Finset.disjoint_left]
          intro x hx hxa
          cases x with
          | inl i => exact inl_not_mem_embeddedAtom H i hxa
          | inr h => simpa using hx
      | large =>
          right
          intro x hxa
          cases x with
          | inl i => exact False.elim (inl_not_mem_embeddedAtom H i hxa)
          | inr h => simp [realizeTemplate]

/-- No strict extension of the embedded atom remains an all-or-none block. -/
theorem parameterized56_atom_maximal
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    ∀ K, embeddedAtom H ⊂ K →
      ¬ IsAtomBlock (parameterized56 H) K := by
  intro K hHK hblock
  rcases Finset.exists_of_ssubset hHK with ⟨z, hzK, hznot⟩
  have hAtomK : embeddedAtom H ⊆ K := hHK.le
  cases z with
  | inl i =>
      let B := realizeTemplate H (cycleEdgeTemplate i)
      have hBLayer : B ∈ parameterized56Layers H 2 :=
        Finset.mem_image.mpr
          ⟨cycleEdgeTemplate i, cycleEdgeTemplate_mem_layer2 i, rfl⟩
      have hBFamily : B ∈ parameterized56 H :=
        (mem_layerUnion (parameterized56Layers H) B).mpr ⟨2, hBLayer⟩
      have hiB : Sum.inl i ∈ B := by
        exact (inl_mem_realizeTemplate_iff H i
          (cycleEdgeTemplate i)).mpr (self_mem_cycleEdgeTemplate_core i)
      rcases hblock B hBFamily with hdisj | hKB
      · exact Finset.disjoint_left.mp hdisj hiB hzK
      · let h0 : H := Classical.choice (nonempty_of_vor hH)
        have hhK : Sum.inr h0 ∈ K :=
          hAtomK (inr_mem_embeddedAtom H h0)
        have hhB := hKB hhK
        simpa [B, cycleEdgeTemplate, realizeTemplate] using hhB
  | inr h =>
      exact hznot (inr_mem_embeddedAtom H h)

/-- The embedded copy of `H` is a homogeneous atom in the exact source sense:
blockness, maximality, and cardinality greater than two. -/
theorem parameterized56_homogeneousAtom
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    IsHomogeneousAtom (parameterized56 H) (embeddedAtom H) := by
  exact ⟨⟨parameterized56_atomBlock,
      parameterized56_atom_maximal hH⟩,
    by simpa using hH⟩

/-- The generic family saturation theorem.  Its only construction-level
dependency is the F3B layered saturated-antichain theorem. -/
theorem parameterized56_saturated
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    IsSaturatedKSperner 7 (parameterized56 H) := by
  exact layered_saturated_antichains
    (k := 7) (by omega)
    (parameterized56Layers H)
    (parameterized56_layers_saturated hH)
    (parameterized56_layers_pairwiseDisjoint hH)
    (parameterized56_layers_layered hH)

/-- Bundled parameterized theorem: saturation, exact cardinality, and the
homogeneous-atom conclusion for every legal finite atom type. -/
theorem parameterized56_full
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    IsSaturatedKSperner 7 (parameterized56 H) ∧
      (parameterized56 H).card = 56 ∧
      IsHomogeneousAtom (parameterized56 H) (embeddedAtom H) :=
  ⟨parameterized56_saturated hH,
    parameterized56_card hH,
    parameterized56_homogeneousAtom hH⟩

end AiMathLab.P0053Parameterized56
