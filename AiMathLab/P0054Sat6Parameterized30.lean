import AiMathLab.SaturatedSperner.ParameterizedAtom

/-!
# The parameterized thirty-member saturated 6-Sperner family

This is the construction of Morrison--Noel--Scott, Proposition 20.  The six
fixed core points are ordered as `x₁,x₂,y₁,y₂,w,z`.  Every template
contains either none or all of the variable homogeneous atom.
-/

universe u

namespace AiMathLab.P0054.Sat6Parameterized30

open AiMathLab.SaturatedSperner
open AiMathLab.SaturatedSperner.ParameterizedAtom

abbrev T := Template 6

def coreFromMask (m : Fin 64) : Finset (Fin 6) :=
  Finset.univ.filter fun i => m.val.testBit i.val

def small (m : Fin 64) : T := ⟨coreFromMask m, .small⟩
def large (m : Fin 64) : T := ⟨coreFromMask m, .large⟩

/- The six exact layers.  In layers two and three the large templates are
the maximal stable sets of the displayed small hypergraphs. -/
def sourceRows : Fin 6 → List T := ![
  [small 0],
  [small 1, small 2, small 4, small 16, large 40],
  [small 5, small 9, small 6, small 10, small 48,
    large 19, large 35, large 28, large 44],
  [small 21, small 37, small 26, small 42,
    large 15, large 51, large 54, large 57, large 60],
  [small 23, large 62, large 61, large 59, large 47],
  [large 63]
]

def layers (i : Fin 6) : Finset T := (sourceRows i).toFinset

theorem sourceRows_nodup : ∀ i, (sourceRows i).Nodup := by
  decide

theorem sourceRows_sizes :
    (List.ofFn sourceRows).map List.length = [1, 5, 9, 9, 5, 1] := by
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

set_option maxRecDepth 100000 in
private theorem cells3 : ∀ C q, CellResolved layers 3 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem cells4 : ∀ C q, CellResolved layers 4 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem cells5 : ∀ C q, CellResolved layers 5 ⟨C, q⟩ := by
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

theorem template_layers_disjoint :
    ∀ {i j : Fin 6}, i ≠ j → Disjoint (layers i) (layers j) := by
  decide

set_option maxRecDepth 100000 in
private theorem template_layers_layered_fin :
    ∀ (i : Fin 5) (t : T),
      t ∈ layers ⟨i.val + 1, by omega⟩ →
        ∃ s ∈ layers ⟨i.val, by omega⟩, TemplateLT s t := by
  decide

theorem template_layers_layered :
    ∀ (i : Nat) (hi : i + 1 < 6) (t : T),
      t ∈ layers ⟨i + 1, hi⟩ →
        ∃ s ∈ layers ⟨i, by omega⟩, TemplateLT s t := by
  intro i hi t ht
  let j : Fin 5 := ⟨i, by omega⟩
  have ht' : t ∈ layers ⟨j.val + 1, by omega⟩ := by
    simpa [j] using ht
  rcases template_layers_layered_fin j t ht' with ⟨s, hs, hst⟩
  exact ⟨s, by simpa [j] using hs, hst⟩

theorem small_templates_cover_core :
    ∀ i : Fin 6, ∃ j t, t ∈ layers j ∧
      t.atomUse = .small ∧ i ∈ t.core := by
  decide

theorem template_union_card :
    (Finset.univ.biUnion layers).card = 30 := by
  decide

abbrev ParamGround (H : Type u) := Ground 6 H

def family
    (H : Type u) [Fintype H] [DecidableEq H] : Family (ParamGround H) :=
  realizedFamily layers H

def atom
    (H : Type u) [Fintype H] [DecidableEq H] : Finset (ParamGround H) :=
  embeddedAtom 6 H

theorem family_card
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) : (family H).card = 30 := by
  rw [family, realizedFamily_card hH]
  exact template_union_card

theorem family_saturated
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) : IsSaturatedKSperner 6 (family H) := by
  exact layered_saturated_antichains
    (k := 6) (by omega)
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
    IsSaturatedKSperner 6 (family H) ∧
      (family H).card = 30 ∧
      IsHomogeneousAtom (family H) (atom H) :=
  ⟨family_saturated hH, family_card hH, family_homogeneousAtom hH⟩

end AiMathLab.P0054.Sat6Parameterized30
