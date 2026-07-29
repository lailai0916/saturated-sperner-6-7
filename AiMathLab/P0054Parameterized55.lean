import AiMathLab.P0054Size55Core
import AiMathLab.SaturatedSperner.ParameterizedAtom

/-!
# Parameterized form of the P0054 fifty-five-member construction

The low eight bits are the fixed core.  In every source mask the top three
bits are either all absent or all present, so they may be replaced by an
arbitrary finite homogeneous atom.
-/

universe u

namespace AiMathLab.P0054.Parameterized55

open AiMathLab.SaturatedSperner
open AiMathLab.SaturatedSperner.ParameterizedAtom

abbrev T := Template 8

def coreFromNat (m : Nat) : Finset (Fin 8) :=
  Finset.univ.filter fun i => m.testBit i.val

def templateOfMask (m : Nat) : T :=
  ⟨coreFromNat m, if m < 256 then .small else .large⟩

def sourceRows : Fin 7 → List T := fun i =>
  (size55LayerMasks.getD i.val []).map templateOfMask

def layers (i : Fin 7) : Finset T := (sourceRows i).toFinset

theorem sourceRows_nodup : ∀ i, (sourceRows i).Nodup := by
  intro i
  fin_cases i <;> decide

theorem sourceRows_sizes :
    (List.ofFn sourceRows).map List.length = [1, 6, 12, 17, 12, 6, 1] := by
  decide

set_option maxRecDepth 100000 in
private theorem cells0 : ∀ C q, CellResolved layers 0 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem cells1 : ∀ C q, CellResolved layers 1 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem cells2 : ∀ C q, CellResolved layers 2 ⟨C, q⟩ := by
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem cells3 : ∀ C q, CellResolved layers 3 ⟨C, q⟩ := by
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem cells4 : ∀ C q, CellResolved layers 4 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem cells5 : ∀ C q, CellResolved layers 5 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem cells6 : ∀ C q, CellResolved layers 6 ⟨C, q⟩ := by
  decide

theorem cells : ∀ i C q, CellResolved layers i ⟨C, q⟩ := by
  intro i
  fin_cases i
  · exact cells0
  · exact cells1
  · exact cells2
  · exact cells3
  · exact cells4
  · exact cells5
  · exact cells6

set_option maxRecDepth 100000 in
theorem template_layers_disjoint :
    ∀ {i j : Fin 7}, i ≠ j → Disjoint (layers i) (layers j) := by
  decide

set_option maxRecDepth 100000 in
private theorem template_layers_layered_fin :
    ∀ (i : Fin 6) (t : T),
      t ∈ layers ⟨i.val + 1, by omega⟩ →
        ∃ s ∈ layers ⟨i.val, by omega⟩, TemplateLT s t := by
  decide

theorem template_layers_layered :
    ∀ (i : Nat) (hi : i + 1 < 7) (t : T),
      t ∈ layers ⟨i + 1, hi⟩ →
        ∃ s ∈ layers ⟨i, by omega⟩, TemplateLT s t := by
  intro i hi t ht
  let j : Fin 6 := ⟨i, by omega⟩
  have ht' : t ∈ layers ⟨j.val + 1, by omega⟩ := by
    simpa [j] using ht
  rcases template_layers_layered_fin j t ht' with ⟨s, hs, hst⟩
  exact ⟨s, by simpa [j] using hs, hst⟩

set_option maxRecDepth 100000 in
theorem small_templates_cover_core :
    ∀ i : Fin 8, ∃ j t, t ∈ layers j ∧
      t.atomUse = .small ∧ i ∈ t.core := by
  decide

set_option maxRecDepth 100000 in
theorem template_union_card :
    (Finset.univ.biUnion layers).card = 55 := by
  decide

abbrev ParamGround (H : Type u) :=
  AiMathLab.SaturatedSperner.ParameterizedAtom.Ground 8 H

def family
    (H : Type u) [Fintype H] [DecidableEq H] :
    AiMathLab.SaturatedSperner.Family (ParamGround H) :=
  realizedFamily layers H

def atom
    (H : Type u) [Fintype H] [DecidableEq H] : Finset (ParamGround H) :=
  embeddedAtom 8 H

theorem family_card
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) : (family H).card = 55 := by
  rw [family, realizedFamily_card hH]
  exact template_union_card

theorem family_saturated
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) : IsSaturatedKSperner 7 (family H) := by
  exact layered_saturated_antichains
    (k := 7) (by omega)
    (realizedLayer layers H)
    (fun i => realizedLayer_saturated_of_cells hH layers cells i)
    (realizedLayers_pairwiseDisjoint_of_templates hH layers
      template_layers_disjoint)
    (realizedLayers_layered_of_templates hH layers template_layers_layered)

theorem family_homogeneousAtom
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) : IsHomogeneousAtom (family H) (atom H) := by
  exact realized_homogeneousAtom_of_small_cover layers H hH
    small_templates_cover_core

theorem full_certificate
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    IsSaturatedKSperner 7 (family H) ∧
      (family H).card = 55 ∧
      IsHomogeneousAtom (family H) (atom H) :=
  ⟨family_saturated hH, family_card hH, family_homogeneousAtom hH⟩

end AiMathLab.P0054.Parameterized55
