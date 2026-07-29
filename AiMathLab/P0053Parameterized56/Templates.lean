import AiMathLab.SaturatedSperner.Layered

/-!
# The parameterized Martin--Veldt 56-template table

The seven core points use values `0,...,6`, corresponding to source labels
`1,...,7`.  A template records whether it contains none (`small`) or all
(`large`) of the parameter atom.  The raw ordered lists are retained so that
duplicate literals cannot be hidden by conversion to `Finset`.
-/

universe v

namespace AiMathLab.P0053Parameterized56

open AiMathLab.SaturatedSperner

/-- The parameterized ground set: seven fixed core points and an atom `H`. -/
abbrev ParamGround (H : Type v) := Fin 7 ⊕ H

/-- A source template contains either none or all of the parameter atom. -/
inductive AtomUse where
  | small
  | large
deriving DecidableEq

instance : Fintype AtomUse :=
  ⟨{.small, .large}, by
    intro u
    cases u <;> simp⟩

/-- A seven-point core together with its small/large atom flag. -/
structure Template where
  core : Finset (Fin 7)
  atomUse : AtomUse
deriving DecidableEq

private def templateProdEquiv :
    (Finset (Fin 7) × AtomUse) ≃ Template where
  toFun p := ⟨p.1, p.2⟩
  invFun t := (t.core, t.atomUse)
  left_inv p := by cases p; rfl
  right_inv t := by cases t; rfl

instance : Fintype Template :=
  Fintype.ofEquiv (Finset (Fin 7) × AtomUse) templateProdEquiv

theorem template_eq_iff (s t : Template) :
    s = t ↔ s.core = t.core ∧ s.atomUse = t.atomUse := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hcore, huse⟩
    cases s
    cases t
    simp_all

/-- Decode a seven-bit core mask.  The `Fin 128` type rules out high bits. -/
def coreFromMask (m : Fin 128) : Finset (Fin 7) :=
  Finset.univ.filter fun i => m.val.testBit i.val

/-- A source template containing no atom point. -/
def smallMask (m : Fin 128) : Template :=
  ⟨coreFromMask m, .small⟩

/-- A source template containing every atom point. -/
def largeMask (m : Fin 128) : Template :=
  ⟨coreFromMask m, .large⟩

/-- The exact ordered 56-row source table.  Entry order is part of the
canonical readback serialization used by the independent regression test. -/
def sourceRows : Fin 7 → List Template := ![
  [smallMask 0],
  [smallMask 2, smallMask 4, smallMask 16, smallMask 32,
    smallMask 64, largeMask 9],
  [smallMask 3, smallMask 6, smallMask 12, smallMask 24,
    smallMask 48, smallMask 96, smallMask 65,
    largeMask 84, largeMask 41, largeMask 82, largeMask 37,
    largeMask 74, largeMask 21, largeMask 42],
  [smallMask 35, smallMask 70, smallMask 13, smallMask 26,
    smallMask 52, smallMask 104, smallMask 81,
    largeMask 92, largeMask 57, largeMask 114, largeMask 101,
    largeMask 75, largeMask 23, largeMask 46],
  [largeMask 124, largeMask 121, largeMask 115, largeMask 103,
    largeMask 79, largeMask 31, largeMask 62,
    smallMask 43, smallMask 86, smallMask 45, smallMask 90,
    smallMask 53, smallMask 106, smallMask 85],
  [largeMask 125, largeMask 123, largeMask 111, largeMask 95,
    largeMask 63, smallMask 118],
  [largeMask 127]
]

/-- The seven source layer sizes. -/
def layerSize : Fin 7 → Nat := ![1, 6, 14, 14, 14, 6, 1]

/-- One source layer, with the raw-list audit retained separately. -/
def templateLayer (i : Fin 7) : Finset Template :=
  (sourceRows i).toFinset

/-- The ordered concatenation of all seven rows. -/
def templateTable : List Template :=
  (List.ofFn sourceRows).flatten

/-- The set of all 56 source templates. -/
def templateUnion : Finset Template :=
  templateTable.toFinset

theorem sourceRows_nodup :
    ∀ i : Fin 7, (sourceRows i).Nodup := by
  decide

theorem sourceRows_length :
    ∀ i : Fin 7, (sourceRows i).length = layerSize i := by
  decide

theorem templateTable_length : templateTable.length = 56 := by
  decide

theorem templateTable_nodup : templateTable.Nodup := by
  decide

theorem templateLayer_card (i : Fin 7) :
    (templateLayer i).card = layerSize i := by
  rw [templateLayer, List.toFinset_card_of_nodup (sourceRows_nodup i)]
  exact sourceRows_length i

theorem templateUnion_card : templateUnion.card = 56 := by
  rw [templateUnion, List.toFinset_card_of_nodup templateTable_nodup]
  exact templateTable_length

theorem templateUnion_eq_layerUnion :
    templateUnion = Finset.univ.biUnion templateLayer := by
  decide

/-- Template containment, including the atom direction. -/
def TemplateLE (s t : Template) : Prop :=
  s.core ⊆ t.core ∧
    (s.atomUse = .large → t.atomUse = .large)

/-- Strict template containment. -/
def TemplateLT (s t : Template) : Prop :=
  TemplateLE s t ∧ s ≠ t

/-- Full pairwise disjointness of the seven template layers. -/
def PairwiseDisjointTemplateLayers : Prop :=
  ∀ ⦃i j : Fin 7⦄, i ≠ j →
    Disjoint (templateLayer i) (templateLayer j)

theorem templateLayers_pairwiseDisjoint :
    PairwiseDisjointTemplateLayers := by
  unfold PairwiseDisjointTemplateLayers
  decide

/-- Every non-bottom source template has a strict predecessor in the previous
source layer.  This is the complete 50-template predecessor certificate. -/
def TemplateLayersLayered : Prop :=
  ∀ (i : Fin 6) (t : Template),
    t ∈ templateLayer ⟨i.val + 1, by omega⟩ →
      ∃ s : Template,
        s ∈ templateLayer ⟨i.val, by omega⟩ ∧ TemplateLT s t

set_option maxRecDepth 100000 in
theorem templateLayers_layered : TemplateLayersLayered := by
  unfold TemplateLayersLayered TemplateLT TemplateLE
  decide

/-- Complement both the seven-point core and the atom flag. -/
def complementTemplate (t : Template) : Template :=
  ⟨Finset.univ \ t.core,
    match t.atomUse with
    | .small => .large
    | .large => .small⟩

/-- Reverse the seven source layers. -/
def reverseLayer (i : Fin 7) : Fin 7 :=
  ⟨6 - i.val, by omega⟩

theorem templateLayer_complement (i : Fin 7) :
    templateLayer (reverseLayer i) =
      (templateLayer i).image complementTemplate := by
  fin_cases i <;> decide

/-- Embed the seven core points into the parameterized ground set. -/
def coreEmbedding (H : Type v) : Fin 7 ↪ ParamGround H :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- Embed the atom into the parameterized ground set. -/
def atomEmbedding (H : Type v) : H ↪ ParamGround H :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Embed a seven-point core subset. -/
def embeddedCore (H : Type v) (C : Finset (Fin 7)) :
    Finset (ParamGround H) :=
  C.map (coreEmbedding H)

/-- The embedded copy of the whole atom. -/
def embeddedAtom (H : Type v) [Fintype H] [DecidableEq H] :
    Finset (ParamGround H) :=
  Finset.univ.map (atomEmbedding H)

/-- Realize a source template on `Fin 7 ⊕ H`. -/
def realizeTemplate
    (H : Type v) [Fintype H] [DecidableEq H]
    (t : Template) : Finset (ParamGround H) :=
  match t.atomUse with
  | .small => embeddedCore H t.core
  | .large => embeddedCore H t.core ∪ embeddedAtom H

@[simp] theorem inl_mem_embeddedCore_iff
    (H : Type v) (C : Finset (Fin 7)) (i : Fin 7) :
    Sum.inl i ∈ embeddedCore H C ↔ i ∈ C := by
  simp [embeddedCore, coreEmbedding]

@[simp] theorem inr_not_mem_embeddedCore
    (H : Type v) (C : Finset (Fin 7)) (h : H) :
    Sum.inr h ∉ embeddedCore H C := by
  simp [embeddedCore, coreEmbedding]

@[simp] theorem inl_not_mem_embeddedAtom
    (H : Type v) [Fintype H] [DecidableEq H] (i : Fin 7) :
    Sum.inl i ∉ embeddedAtom H := by
  simp [embeddedAtom, atomEmbedding]

@[simp] theorem inr_mem_embeddedAtom
    (H : Type v) [Fintype H] [DecidableEq H] (h : H) :
    Sum.inr h ∈ embeddedAtom H := by
  simp [embeddedAtom, atomEmbedding]

@[simp] theorem inl_mem_realizeTemplate_iff
    (H : Type v) [Fintype H] [DecidableEq H]
    (i : Fin 7) (t : Template) :
    Sum.inl i ∈ realizeTemplate H t ↔ i ∈ t.core := by
  cases t with
  | mk C use => cases use <;> simp [realizeTemplate]

@[simp] theorem inr_mem_realizeTemplate_iff
    (H : Type v) [Fintype H] [DecidableEq H]
    (h : H) (t : Template) :
    Sum.inr h ∈ realizeTemplate H t ↔ t.atomUse = .large := by
  cases t with
  | mk C use => cases use <;> simp [realizeTemplate]

theorem nonempty_of_vor
    {H : Type v} [Fintype H]
    (hH : 2 < Fintype.card H) : Nonempty H :=
  Fintype.card_pos_iff.mp (by omega)

theorem realizeTemplate_eq_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (s t : Template) :
    realizeTemplate H s = realizeTemplate H t ↔ s = t := by
  constructor
  · intro heq
    apply (template_eq_iff s t).mpr
    refine ⟨?_, ?_⟩
    · ext i
      rw [← inl_mem_realizeTemplate_iff H i s,
        ← inl_mem_realizeTemplate_iff H i t, heq]
    · let h0 : H := Classical.choice (nonempty_of_vor hH)
      have hinr :
          (Sum.inr h0 ∈ realizeTemplate H s) ↔
            Sum.inr h0 ∈ realizeTemplate H t := by
        rw [heq]
      cases hs : s.atomUse <;> cases ht : t.atomUse <;>
        simp [inr_mem_realizeTemplate_iff, hs, ht] at hinr ⊢
  · rintro rfl
    rfl

theorem realizeTemplate_injective
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    Function.Injective (realizeTemplate H) := by
  intro s t hst
  exact (realizeTemplate_eq_iff hH s t).mp hst

theorem realizeTemplate_subset_realizeTemplate_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (s t : Template) :
    realizeTemplate H s ⊆ realizeTemplate H t ↔ TemplateLE s t := by
  constructor
  · intro hsub
    refine ⟨?_, ?_⟩
    · intro i hi
      apply (inl_mem_realizeTemplate_iff H i t).mp
      exact hsub ((inl_mem_realizeTemplate_iff H i s).mpr hi)
    · intro hslarge
      let h0 : H := Classical.choice (nonempty_of_vor hH)
      apply (inr_mem_realizeTemplate_iff H h0 t).mp
      exact hsub ((inr_mem_realizeTemplate_iff H h0 s).mpr hslarge)
  · rintro ⟨hcore, hatom⟩ x hx
    cases x with
    | inl i =>
        apply (inl_mem_realizeTemplate_iff H i t).mpr
        exact hcore ((inl_mem_realizeTemplate_iff H i s).mp hx)
    | inr h =>
        apply (inr_mem_realizeTemplate_iff H h t).mpr
        exact hatom ((inr_mem_realizeTemplate_iff H h s).mp hx)

theorem realizeTemplate_ssubset_realizeTemplate_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (s t : Template) :
    realizeTemplate H s ⊂ realizeTemplate H t ↔ TemplateLT s t := by
  rw [ssubset_iff_subset_ne, TemplateLT,
    realizeTemplate_subset_realizeTemplate_iff hH]
  exact and_congr_right fun _ => not_congr (realizeTemplate_eq_iff hH s t)

/-- The seven realized source layers. -/
def parameterized56Layers
    (H : Type v) [Fintype H] [DecidableEq H]
    (i : Fin 7) : Family (ParamGround H) :=
  (templateLayer i).image (realizeTemplate H)

/-- The union of all seven realized layers. -/
def parameterized56
    (H : Type v) [Fintype H] [DecidableEq H] :
    Family (ParamGround H) :=
  LayerUnion (parameterized56Layers H)

theorem parameterized56_eq_image_templateUnion
    (H : Type v) [Fintype H] [DecidableEq H] :
    parameterized56 H = templateUnion.image (realizeTemplate H) := by
  calc
    parameterized56 H =
        Finset.univ.biUnion fun i =>
          (templateLayer i).image (realizeTemplate H) := rfl
    _ = (Finset.univ.biUnion templateLayer).image (realizeTemplate H) :=
      Finset.biUnion_image.symm
    _ = templateUnion.image (realizeTemplate H) := by
      rw [templateUnion_eq_layerUnion]

theorem parameterized56_layer_card
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (i : Fin 7) :
    (parameterized56Layers H i).card = layerSize i := by
  rw [parameterized56Layers,
    Finset.card_image_of_injective _ (realizeTemplate_injective hH)]
  exact templateLayer_card i

theorem parameterized56_card_from_templates
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    (parameterized56 H).card = 56 := by
  rw [parameterized56_eq_image_templateUnion,
    Finset.card_image_of_injective _ (realizeTemplate_injective hH)]
  exact templateUnion_card

@[simp] theorem embeddedAtom_card
    (H : Type v) [Fintype H] [DecidableEq H] :
    (embeddedAtom H).card = Fintype.card H := by
  simp [embeddedAtom]

theorem realize_complementTemplate
    (H : Type v) [Fintype H] [DecidableEq H] (t : Template) :
    realizeTemplate H (complementTemplate t) =
      (Finset.univ : Finset (ParamGround H)) \ realizeTemplate H t := by
  ext x
  cases x with
  | inl i =>
      cases ht : t.atomUse <;>
        simp [complementTemplate, realizeTemplate, ht]
  | inr h =>
      cases ht : t.atomUse <;>
        simp [complementTemplate, realizeTemplate, ht]

end AiMathLab.P0053Parameterized56
