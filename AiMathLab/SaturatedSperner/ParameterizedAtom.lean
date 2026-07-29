import AiMathLab.SaturatedSperner.HomogeneousAtom
import AiMathLab.SaturatedSperner.Layered

/-!
# Finite-core families with one parameter atom

This file packages the three-state reduction shared by parameterized
constructions.  A template records a subset of a fixed finite core and
whether it uses none or all of a second, variable finite type.  Comparisons
with an arbitrary subset then depend only on the core projection and on
whether its atom projection is empty, partial, or full.
-/

universe u

namespace AiMathLab.SaturatedSperner.ParameterizedAtom

open AiMathLab.SaturatedSperner

inductive AtomUse where
  | small
  | large
deriving DecidableEq

instance : Fintype AtomUse :=
  ⟨{.small, .large}, by intro u; cases u <;> simp⟩

structure Template (c : Nat) where
  core : Finset (Fin c)
  atomUse : AtomUse
deriving DecidableEq

private def templateEquiv (c : Nat) :
    (Finset (Fin c) × AtomUse) ≃ Template c where
  toFun p := ⟨p.1, p.2⟩
  invFun t := (t.core, t.atomUse)
  left_inv p := by cases p; rfl
  right_inv t := by cases t; rfl

instance (c : Nat) : Fintype (Template c) :=
  Fintype.ofEquiv (Finset (Fin c) × AtomUse) (templateEquiv c)

theorem template_eq_iff {c : Nat} (s t : Template c) :
    s = t ↔ s.core = t.core ∧ s.atomUse = t.atomUse := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hc, hu⟩
    cases s
    cases t
    simp_all

abbrev Ground (c : Nat) (H : Type u) := Fin c ⊕ H

def coreEmbedding (c : Nat) (H : Type u) : Fin c ↪ Ground c H :=
  ⟨Sum.inl, Sum.inl_injective⟩

def atomEmbedding (c : Nat) (H : Type u) : H ↪ Ground c H :=
  ⟨Sum.inr, Sum.inr_injective⟩

def embeddedCore (H : Type u) (C : Finset (Fin c)) :
    Finset (Ground c H) :=
  C.map (coreEmbedding c H)

def embeddedAtom (c : Nat) (H : Type u) [Fintype H] [DecidableEq H] :
    Finset (Ground c H) :=
  Finset.univ.map (atomEmbedding c H)

def realize
    (H : Type u) [Fintype H] [DecidableEq H]
    (t : Template c) : Finset (Ground c H) :=
  match t.atomUse with
  | .small => embeddedCore H t.core
  | .large => embeddedCore H t.core ∪ embeddedAtom c H

@[simp] theorem inl_mem_embeddedCore_iff
    (H : Type u) (C : Finset (Fin c)) (i : Fin c) :
    Sum.inl i ∈ embeddedCore H C ↔ i ∈ C := by
  simp [embeddedCore, coreEmbedding]

@[simp] theorem inr_not_mem_embeddedCore
    (H : Type u) (C : Finset (Fin c)) (h : H) :
    Sum.inr h ∉ embeddedCore H C := by
  simp [embeddedCore, coreEmbedding]

@[simp] theorem inl_not_mem_embeddedAtom
    (c : Nat) (H : Type u) [Fintype H] [DecidableEq H] (i : Fin c) :
    Sum.inl i ∉ embeddedAtom c H := by
  simp [embeddedAtom, atomEmbedding]

@[simp] theorem inr_mem_embeddedAtom
    (c : Nat) (H : Type u) [Fintype H] [DecidableEq H] (h : H) :
    Sum.inr h ∈ embeddedAtom c H := by
  simp [embeddedAtom, atomEmbedding]

@[simp] theorem inl_mem_realize_iff
    (H : Type u) [Fintype H] [DecidableEq H]
    (i : Fin c) (t : Template c) :
    Sum.inl i ∈ realize H t ↔ i ∈ t.core := by
  cases t with
  | mk C use => cases use <;> simp [realize]

@[simp] theorem inr_mem_realize_iff
    (H : Type u) [Fintype H] [DecidableEq H]
    (h : H) (t : Template c) :
    Sum.inr h ∈ realize H t ↔ t.atomUse = .large := by
  cases t with
  | mk C use => cases use <;> simp [realize]

theorem nonempty_of_two_lt_card
    {H : Type u} [Fintype H] (hH : 2 < Fintype.card H) : Nonempty H :=
  Fintype.card_pos_iff.mp (by omega)

theorem realize_eq_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (s t : Template c) :
    realize H s = realize H t ↔ s = t := by
  constructor
  · intro heq
    apply (template_eq_iff s t).mpr
    refine ⟨?_, ?_⟩
    · ext i
      rw [← inl_mem_realize_iff H i s,
        ← inl_mem_realize_iff H i t, heq]
    · let h0 : H := Classical.choice (nonempty_of_two_lt_card hH)
      have hinr :
          (Sum.inr h0 ∈ realize H s) ↔ Sum.inr h0 ∈ realize H t := by
        rw [heq]
      cases hs : s.atomUse <;> cases ht : t.atomUse <;>
        simp [inr_mem_realize_iff, hs, ht] at hinr ⊢
  · rintro rfl
    rfl

theorem realize_injective
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) : Function.Injective (realize H : Template c → _) := by
  intro s t hst
  exact (realize_eq_iff hH s t).mp hst

def TemplateLE (s t : Template c) : Prop :=
  s.core ⊆ t.core ∧ (s.atomUse = .large → t.atomUse = .large)

def TemplateLT (s t : Template c) : Prop :=
  TemplateLE s t ∧ s ≠ t

instance (s t : Template c) : Decidable (TemplateLE s t) := by
  unfold TemplateLE
  infer_instance

instance (s t : Template c) : Decidable (TemplateLT s t) := by
  unfold TemplateLT
  infer_instance

theorem realize_subset_realize_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (s t : Template c) :
    realize H s ⊆ realize H t ↔ TemplateLE s t := by
  constructor
  · intro hsub
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (inl_mem_realize_iff H i t).mp
        (hsub ((inl_mem_realize_iff H i s).mpr hi))
    · intro hs
      let h0 : H := Classical.choice (nonempty_of_two_lt_card hH)
      exact (inr_mem_realize_iff H h0 t).mp
        (hsub ((inr_mem_realize_iff H h0 s).mpr hs))
  · rintro ⟨hc, hu⟩ x hx
    cases x with
    | inl i =>
        exact (inl_mem_realize_iff H i t).mpr
          (hc ((inl_mem_realize_iff H i s).mp hx))
    | inr h =>
        exact (inr_mem_realize_iff H h t).mpr
          (hu ((inr_mem_realize_iff H h s).mp hx))

theorem realize_ssubset_realize_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (s t : Template c) :
    realize H s ⊂ realize H t ↔ TemplateLT s t := by
  rw [ssubset_iff_subset_ne, TemplateLT,
    realize_subset_realize_iff hH]
  exact and_congr_right fun _ => not_congr (realize_eq_iff hH s t)

def realizedLayer
    (L : Fin k → Finset (Template c))
    (H : Type u) [Fintype H] [DecidableEq H]
    (i : Fin k) : Family (Ground c H) :=
  (L i).image (realize H)

def realizedFamily
    (L : Fin k → Finset (Template c))
    (H : Type u) [Fintype H] [DecidableEq H] : Family (Ground c H) :=
  LayerUnion (realizedLayer L H)

theorem realizedFamily_eq_image
    (L : Fin k → Finset (Template c))
    (H : Type u) [Fintype H] [DecidableEq H] :
    realizedFamily L H =
      (Finset.univ.biUnion L).image (realize H) := by
  calc
    realizedFamily L H =
        Finset.univ.biUnion fun i => (L i).image (realize H) := rfl
    _ = (Finset.univ.biUnion L).image (realize H) :=
      Finset.biUnion_image.symm

theorem realizedFamily_card
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (L : Fin k → Finset (Template c)) :
    (realizedFamily L H).card = (Finset.univ.biUnion L).card := by
  rw [realizedFamily_eq_image,
    Finset.card_image_of_injective _ (realize_injective hH)]

theorem realizedLayer_card
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (L : Fin k → Finset (Template c)) (i : Fin k) :
    (realizedLayer L H i).card = (L i).card := by
  rw [realizedLayer, Finset.card_image_of_injective _ (realize_injective hH)]

def coreProjection
    {H : Type u} [DecidableEq H]
    (S : Finset (Ground c H)) : Finset (Fin c) :=
  Finset.univ.filter fun i => Sum.inl i ∈ S

def atomProjection
    {H : Type u} [Fintype H] [DecidableEq H]
    (S : Finset (Ground c H)) : Finset H :=
  Finset.univ.filter fun h => Sum.inr h ∈ S

inductive AtomState where
  | empty
  | mixed
  | full
deriving DecidableEq

instance : Fintype AtomState :=
  ⟨{.empty, .mixed, .full}, by intro q; cases q <;> simp⟩

def atomState
    {H : Type u} [Fintype H] [DecidableEq H]
    (S : Finset (Ground c H)) : AtomState :=
  if atomProjection S = ∅ then .empty
  else if atomProjection S = Finset.univ then .full
  else .mixed

structure Signature (c : Nat) where
  core : Finset (Fin c)
  state : AtomState
deriving DecidableEq

def signature
    {H : Type u} [Fintype H] [DecidableEq H]
    (S : Finset (Ground c H)) : Signature c :=
  ⟨coreProjection S, atomState S⟩

@[simp] theorem mem_coreProjection_iff
    {H : Type u} [DecidableEq H] (i : Fin c) (S : Finset (Ground c H)) :
    i ∈ coreProjection S ↔ Sum.inl i ∈ S := by
  simp [coreProjection]

@[simp] theorem mem_atomProjection_iff
    {H : Type u} [Fintype H] [DecidableEq H] (h : H) (S : Finset (Ground c H)) :
    h ∈ atomProjection S ↔ Sum.inr h ∈ S := by
  simp [atomProjection]

theorem atomState_eq_empty_iff
    {H : Type u} [Fintype H] [DecidableEq H] (S : Finset (Ground c H)) :
    atomState S = .empty ↔ atomProjection S = ∅ := by
  unfold atomState
  by_cases hE : atomProjection S = ∅
  · rw [if_pos hE]
    exact ⟨fun _ => hE, fun _ => rfl⟩
  · rw [if_neg hE]
    by_cases hF : atomProjection S = Finset.univ
    · rw [if_pos hF]
      constructor
      · intro h
        cases h
      · intro h
        exact False.elim (hE h)
    · rw [if_neg hF]
      constructor
      · intro h
        cases h
      · intro h
        exact False.elim (hE h)

theorem atomState_eq_mixed_iff
    {H : Type u} [Fintype H] [DecidableEq H] (S : Finset (Ground c H)) :
    atomState S = .mixed ↔
      atomProjection S ≠ ∅ ∧ atomProjection S ≠ Finset.univ := by
  unfold atomState
  by_cases hE : atomProjection S = ∅
  · rw [if_pos hE]
    constructor
    · intro h
      cases h
    · intro h
      exact False.elim (h.1 hE)
  · rw [if_neg hE]
    by_cases hF : atomProjection S = Finset.univ
    · rw [if_pos hF]
      constructor
      · intro h
        cases h
      · intro h
        exact False.elim (h.2 hF)
    · rw [if_neg hF]
      exact ⟨fun _ => ⟨hE, hF⟩, fun _ => rfl⟩

theorem atomState_eq_full_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (S : Finset (Ground c H)) :
    atomState S = .full ↔ atomProjection S = Finset.univ := by
  letI : Nonempty H := nonempty_of_two_lt_card hH
  let h0 : H := Classical.choice inferInstance
  have hne : (Finset.univ : Finset H) ≠ ∅ := by
    intro heq
    have : h0 ∈ (Finset.univ : Finset H) := Finset.mem_univ h0
    rw [heq] at this
    simpa using this
  unfold atomState
  by_cases hE : atomProjection S = ∅
  · rw [if_pos hE]
    have hF : atomProjection S ≠ Finset.univ := fun h => hne (h.symm.trans hE)
    constructor
    · intro h
      cases h
    · intro h
      exact False.elim (hF h)
  · rw [if_neg hE]
    by_cases hF : atomProjection S = Finset.univ
    · rw [if_pos hF]
      exact ⟨fun _ => hF, fun _ => rfl⟩
    · rw [if_neg hF]
      constructor
      · intro h
        cases h
      · intro h
        exact False.elim (hF h)

def expectedState : AtomUse → AtomState
  | .small => .empty
  | .large => .full

theorem coreProjection_realize
    {H : Type u} [Fintype H] [DecidableEq H] (t : Template c) :
    coreProjection (realize H t) = t.core := by
  ext i
  simp

theorem atomState_realize
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (t : Template c) :
    atomState (realize H t) = expectedState t.atomUse := by
  cases t with
  | mk C use =>
      cases use with
      | small =>
          apply (atomState_eq_empty_iff _).mpr
          ext h
          simp [atomProjection, realize]
      | large =>
          apply (atomState_eq_full_iff hH _).mpr
          ext h
          simp [atomProjection, realize]

def atomSubsetTemplate : AtomState → AtomUse → Prop
  | .empty, .small => True
  | .mixed, .small => False
  | .full, .small => False
  | _, .large => True

def templateAtomSubset : AtomUse → AtomState → Prop
  | .small, _ => True
  | .large, .full => True
  | .large, .empty => False
  | .large, .mixed => False

def signatureEqTemplate (s : Signature c) (t : Template c) : Prop :=
  s.core = t.core ∧ s.state = expectedState t.atomUse

def signatureSubsetTemplate (s : Signature c) (t : Template c) : Prop :=
  s.core ⊆ t.core ∧ atomSubsetTemplate s.state t.atomUse

def templateSubsetSignature (t : Template c) (s : Signature c) : Prop :=
  t.core ⊆ s.core ∧ templateAtomSubset t.atomUse s.state

def signatureStrictSubsetTemplate (s : Signature c) (t : Template c) : Prop :=
  signatureSubsetTemplate s t ∧ ¬ signatureEqTemplate s t

def templateStrictSubsetSignature (t : Template c) (s : Signature c) : Prop :=
  templateSubsetSignature t s ∧ ¬ signatureEqTemplate s t

def signatureComparable (s : Signature c) (t : Template c) : Prop :=
  signatureStrictSubsetTemplate s t ∨ templateStrictSubsetSignature t s

instance (q : AtomState) (a : AtomUse) : Decidable (atomSubsetTemplate q a) := by
  cases q <;> cases a
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id
  · exact isTrue trivial
  · exact isFalse id
  · exact isTrue trivial

instance (a : AtomUse) (q : AtomState) : Decidable (templateAtomSubset a q) := by
  cases a <;> cases q
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id
  · exact isFalse id
  · exact isTrue trivial

instance (s : Signature c) (t : Template c) : Decidable (signatureEqTemplate s t) := by
  unfold signatureEqTemplate
  infer_instance

instance (s : Signature c) (t : Template c) : Decidable (signatureSubsetTemplate s t) := by
  unfold signatureSubsetTemplate
  infer_instance

instance (t : Template c) (s : Signature c) : Decidable (templateSubsetSignature t s) := by
  unfold templateSubsetSignature
  infer_instance

instance (s : Signature c) (t : Template c) : Decidable (signatureStrictSubsetTemplate s t) := by
  unfold signatureStrictSubsetTemplate
  infer_instance

instance (t : Template c) (s : Signature c) : Decidable (templateStrictSubsetSignature t s) := by
  unfold templateStrictSubsetSignature
  infer_instance

instance (s : Signature c) (t : Template c) : Decidable (signatureComparable s t) := by
  unfold signatureComparable
  infer_instance

theorem eq_realize_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (S : Finset (Ground c H)) (t : Template c) :
    S = realize H t ↔ signatureEqTemplate (signature S) t := by
  constructor
  · rintro rfl
    exact ⟨coreProjection_realize t, atomState_realize hH t⟩
  · rintro ⟨hcore, hstate⟩
    change coreProjection S = t.core at hcore
    change atomState S = expectedState t.atomUse at hstate
    ext x
    cases x with
    | inl i =>
        rw [inl_mem_realize_iff, ← mem_coreProjection_iff]
        exact Finset.ext_iff.mp hcore i
    | inr h =>
        rw [inr_mem_realize_iff]
        cases hu : t.atomUse with
        | small =>
            have hs : atomState S = .empty := by
              simpa [expectedState, hu] using hstate
            have hp := (atomState_eq_empty_iff S).mp hs
            constructor
            · intro hx
              have hh := (mem_atomProjection_iff h S).mpr hx
              simpa [hp] using hh
            · simp [hu]
        | large =>
            have hs : atomState S = .full := by
              simpa [expectedState, hu] using hstate
            have hp := (atomState_eq_full_iff hH S).mp hs
            constructor
            · intro _
              rfl
            · intro _
              apply (mem_atomProjection_iff h S).mp
              rw [hp]
              exact Finset.mem_univ h

theorem subset_realize_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (S : Finset (Ground c H)) (t : Template c) :
    S ⊆ realize H t ↔ signatureSubsetTemplate (signature S) t := by
  constructor
  · intro hsub
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (inl_mem_realize_iff H i t).mp
        (hsub ((mem_coreProjection_iff i S).mp hi))
    · change atomSubsetTemplate (atomState S) t.atomUse
      cases hs : atomState S <;> cases hu : t.atomUse
      · simp [atomSubsetTemplate]
      · simp [atomSubsetTemplate]
      · exfalso
        have hp : atomProjection S ≠ ∅ :=
          (atomState_eq_mixed_iff S).mp hs |>.1
        rcases Finset.nonempty_iff_ne_empty.mpr hp with ⟨h, hh⟩
        have hx := hsub ((mem_atomProjection_iff h S).mp hh)
        simpa [hu] using hx
      · simp [atomSubsetTemplate]
      · exfalso
        let h0 : H := Classical.choice (nonempty_of_two_lt_card hH)
        have hp := (atomState_eq_full_iff hH S).mp hs
        have hh : h0 ∈ atomProjection S := by simp [hp]
        have hx := hsub ((mem_atomProjection_iff h0 S).mp hh)
        simpa [hu] using hx
      · simp [atomSubsetTemplate]
  · rintro ⟨hcore, hatom⟩ x hx
    change coreProjection S ⊆ t.core at hcore
    change atomSubsetTemplate (atomState S) t.atomUse at hatom
    cases x with
    | inl i =>
        exact (inl_mem_realize_iff H i t).mpr
          (hcore ((mem_coreProjection_iff i S).mpr hx))
    | inr h =>
        cases hs : atomState S <;> cases hu : t.atomUse
        · have hp := (atomState_eq_empty_iff S).mp hs
          have hh := (mem_atomProjection_iff h S).mpr hx
          simpa [hp] using hh
        · exact (inr_mem_realize_iff H h t).mpr hu
        · simp [atomSubsetTemplate, hs, hu] at hatom
        · exact (inr_mem_realize_iff H h t).mpr hu
        · simp [atomSubsetTemplate, hs, hu] at hatom
        · exact (inr_mem_realize_iff H h t).mpr hu

theorem realize_subset_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (S : Finset (Ground c H)) (t : Template c) :
    realize H t ⊆ S ↔ templateSubsetSignature t (signature S) := by
  constructor
  · intro hsub
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (mem_coreProjection_iff i S).mpr
        (hsub ((inl_mem_realize_iff H i t).mpr hi))
    · change templateAtomSubset t.atomUse (atomState S)
      cases hu : t.atomUse <;> cases hs : atomState S
      · simp [templateAtomSubset]
      · simp [templateAtomSubset]
      · simp [templateAtomSubset]
      · exfalso
        let h0 : H := Classical.choice (nonempty_of_two_lt_card hH)
        have hx := hsub ((inr_mem_realize_iff H h0 t).mpr hu)
        have hh := (mem_atomProjection_iff h0 S).mpr hx
        have hp := (atomState_eq_empty_iff S).mp hs
        simpa [hp] using hh
      · exfalso
        have hp : atomProjection S ≠ Finset.univ :=
          (atomState_eq_mixed_iff S).mp hs |>.2
        apply hp
        ext h
        simp only [Finset.mem_univ, iff_true]
        exact (mem_atomProjection_iff h S).mpr
          (hsub ((inr_mem_realize_iff H h t).mpr hu))
      · simp [templateAtomSubset]
  · rintro ⟨hcore, hatom⟩ x hx
    change t.core ⊆ coreProjection S at hcore
    change templateAtomSubset t.atomUse (atomState S) at hatom
    cases x with
    | inl i =>
        exact (mem_coreProjection_iff i S).mp
          (hcore ((inl_mem_realize_iff H i t).mp hx))
    | inr h =>
        have ht := (inr_mem_realize_iff H h t).mp hx
        cases hu : t.atomUse <;> cases hs : atomState S
        · simp [hu] at ht
        · simp [hu] at ht
        · simp [hu] at ht
        · simp [templateAtomSubset, hu, hs] at hatom
        · simp [templateAtomSubset, hu, hs] at hatom
        · have hp := (atomState_eq_full_iff hH S).mp hs
          apply (mem_atomProjection_iff h S).mp
          rw [hp]
          exact Finset.mem_univ h

theorem ssubset_realize_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (S : Finset (Ground c H)) (t : Template c) :
    S ⊂ realize H t ↔ signatureStrictSubsetTemplate (signature S) t := by
  rw [ssubset_iff_subset_ne, signatureStrictSubsetTemplate,
    subset_realize_iff hH]
  exact and_congr_right fun _ => not_congr (eq_realize_iff hH S t)

theorem realize_ssubset_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (S : Finset (Ground c H)) (t : Template c) :
    realize H t ⊂ S ↔ templateStrictSubsetSignature t (signature S) := by
  rw [ssubset_iff_subset_ne, templateStrictSubsetSignature,
    realize_subset_iff hH]
  have heq :
      realize H t = S ↔ signatureEqTemplate (signature S) t := by
    constructor
    · intro h
      exact (eq_realize_iff hH S t).mp h.symm
    · intro h
      exact ((eq_realize_iff hH S t).mpr h).symm
  exact and_congr_right fun _ => not_congr heq

theorem strictComparable_realize_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (S : Finset (Ground c H)) (t : Template c) :
    (S ⊂ realize H t ∨ realize H t ⊂ S) ↔
      signatureComparable (signature S) t := by
  rw [signatureComparable, ssubset_realize_iff hH,
    realize_ssubset_iff hH]

def signatureMember
    (L : Fin k → Finset (Template c)) (i : Fin k) (s : Signature c) : Prop :=
  ∃ t ∈ L i, signatureEqTemplate s t

instance (L : Fin k → Finset (Template c)) (i : Fin k) (s : Signature c) :
    Decidable (signatureMember L i s) := by
  unfold signatureMember
  infer_instance

theorem mem_realizedLayer_iff
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (L : Fin k → Finset (Template c)) (i : Fin k) (S : Finset (Ground c H)) :
    S ∈ realizedLayer L H i ↔ signatureMember L i (signature S) := by
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨t, ht, hreal⟩
    exact ⟨t, ht, (eq_realize_iff hH S t).mp hreal.symm⟩
  · rintro ⟨t, ht, hs⟩
    exact Finset.mem_image.mpr ⟨t, ht, ((eq_realize_iff hH S t).mpr hs).symm⟩

def CellResolved
    (L : Fin k → Finset (Template c)) (i : Fin k) (s : Signature c) : Prop :=
  (signatureMember L i s ∧
      ∀ t ∈ L i, ¬ signatureComparable s t) ∨
  (¬ signatureMember L i s ∧
      ∃ t ∈ L i, signatureComparable s t)

instance (L : Fin k → Finset (Template c)) (i : Fin k) (s : Signature c) :
    Decidable (CellResolved L i s) := by
  unfold CellResolved
  infer_instance

theorem realizedLayer_no_ssubset_of_cells
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (L : Fin k → Finset (Template c))
    (hcells : ∀ i C q, CellResolved L i ⟨C, q⟩)
    (i : Fin k) {A B : Finset (Ground c H)}
    (hA : A ∈ realizedLayer L H i) (hB : B ∈ realizedLayer L H i) :
    ¬ A ⊂ B := by
  intro hAB
  have hAsig := (mem_realizedLayer_iff hH L i A).mp hA
  have hcell := hcells i (coreProjection A) (atomState A)
  change CellResolved L i (signature A) at hcell
  rcases hcell with hm | he
  · rcases Finset.mem_image.mp hB with ⟨t, ht, hreal⟩
    apply hm.2 t ht
    apply (strictComparable_realize_iff hH A t).mp
    exact Or.inl (by simpa [hreal] using hAB)
  · exact False.elim (he.1 hAsig)

theorem realizedLayer_external_comparable_of_cells
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (L : Fin k → Finset (Template c))
    (hcells : ∀ i C q, CellResolved L i ⟨C, q⟩)
    (i : Fin k) {S : Finset (Ground c H)}
    (hS : S ∉ realizedLayer L H i) :
    ∃ T ∈ realizedLayer L H i, T ⊂ S ∨ S ⊂ T := by
  have hSsig : ¬ signatureMember L i (signature S) :=
    fun hs => hS ((mem_realizedLayer_iff hH L i S).mpr hs)
  have hcell := hcells i (coreProjection S) (atomState S)
  change CellResolved L i (signature S) at hcell
  rcases hcell with hm | he
  · exact False.elim (hSsig hm.1)
  · rcases he.2 with ⟨t, ht, hcomp⟩
    have hactual := (strictComparable_realize_iff hH S t).mpr hcomp
    exact ⟨realize H t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hactual.symm⟩

theorem realizedLayer_saturated_of_cells
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (L : Fin k → Finset (Template c))
    (hcells : ∀ i C q, CellResolved L i ⟨C, q⟩)
    (i : Fin k) : IsSaturatedAntichain (realizedLayer L H i) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨B, hB, A, hA, hAB⟩
    exact realizedLayer_no_ssubset_of_cells hH L hcells i hA hB hAB
  · intro S hS
    rcases realizedLayer_external_comparable_of_cells hH L hcells i hS with
      ⟨T, hT, hTS | hST⟩
    · exact ⟨S, Finset.mem_insert_self _ _,
        T, Finset.mem_insert_of_mem hT, hTS⟩
    · exact ⟨T, Finset.mem_insert_of_mem hT,
        S, Finset.mem_insert_self _ _, hST⟩

theorem realizedLayers_pairwiseDisjoint_of_templates
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (L : Fin k → Finset (Template c))
    (hdisj : ∀ {i j : Fin k}, i ≠ j → Disjoint (L i) (L j)) :
    PairwiseDisjointLayers (realizedLayer L H) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro D hDi hDj
  rcases Finset.mem_image.mp hDi with ⟨s, hs, hsD⟩
  rcases Finset.mem_image.mp hDj with ⟨t, ht, htD⟩
  have hst : s = t := realize_injective hH (hsD.trans htD.symm)
  subst t
  exact Finset.disjoint_left.mp (hdisj hij) hs ht

theorem realizedLayers_layered_of_templates
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (L : Fin k → Finset (Template c))
    (hlayered : ∀ (i : Nat) (hi : i + 1 < k) (t : Template c),
      t ∈ L ⟨i + 1, hi⟩ →
        ∃ s ∈ L ⟨i, by omega⟩, TemplateLT s t) :
    IsLayered (realizedLayer L H) := by
  intro i hi D hD
  rcases Finset.mem_image.mp hD with ⟨t, ht, htD⟩
  rcases hlayered i hi t ht with ⟨s, hs, hst⟩
  refine ⟨realize H s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
  rw [← htD]
  exact (realize_ssubset_realize_iff hH s t).mpr hst

@[simp] theorem embeddedAtom_card
    (c : Nat) (H : Type u) [Fintype H] [DecidableEq H] :
    (embeddedAtom c H).card = Fintype.card H := by
  simp [embeddedAtom]

theorem realized_atomBlock
    (L : Fin k → Finset (Template c))
    (H : Type u) [Fintype H] [DecidableEq H] :
    IsAtomBlock (realizedFamily L H) (embeddedAtom c H) := by
  intro S hS
  rcases (mem_layerUnion (realizedLayer L H) S).mp hS with ⟨i, hi⟩
  rcases Finset.mem_image.mp hi with ⟨t, ht, rfl⟩
  cases t with
  | mk C use =>
      cases use with
      | small =>
          left
          rw [Finset.disjoint_left]
          intro x hx hxa
          cases x with
          | inl i => exact inl_not_mem_embeddedAtom c H i hxa
          | inr h => simpa [realize] using hx
      | large =>
          right
          intro x hx
          cases x with
          | inl i => exact False.elim (inl_not_mem_embeddedAtom c H i hx)
          | inr h => simp [realize]

theorem realized_atom_maximal_of_small_cover
    (L : Fin k → Finset (Template c))
    (H : Type u) [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (hcover : ∀ i : Fin c, ∃ j t, t ∈ L j ∧
      t.atomUse = .small ∧ i ∈ t.core) :
    ∀ K, embeddedAtom c H ⊂ K →
      ¬ IsAtomBlock (realizedFamily L H) K := by
  intro K hAK hblock
  rcases Finset.exists_of_ssubset hAK with ⟨z, hzK, hzA⟩
  have hAKsub : embeddedAtom c H ⊆ K := hAK.le
  cases z with
  | inl i =>
      rcases hcover i with ⟨j, t, ht, hsmall, hit⟩
      have hB : realize H t ∈ realizedFamily L H :=
        (mem_layerUnion (realizedLayer L H) _).mpr
          ⟨j, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
      have hiB : Sum.inl i ∈ realize H t :=
        (inl_mem_realize_iff H i t).mpr hit
      rcases hblock (realize H t) hB with hdisj | hKB
      · exact Finset.disjoint_left.mp hdisj hiB hzK
      · let h0 : H := Classical.choice (nonempty_of_two_lt_card hH)
        have hhK : Sum.inr h0 ∈ K := hAKsub (inr_mem_embeddedAtom c H h0)
        have hhB := hKB hhK
        simpa [hsmall] using (inr_mem_realize_iff H h0 t).mp hhB
  | inr h =>
      exact hzA (inr_mem_embeddedAtom c H h)

theorem realized_homogeneousAtom_of_small_cover
    (L : Fin k → Finset (Template c))
    (H : Type u) [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (hcover : ∀ i : Fin c, ∃ j t, t ∈ L j ∧
      t.atomUse = .small ∧ i ∈ t.core) :
    IsHomogeneousAtom (realizedFamily L H) (embeddedAtom c H) := by
  exact ⟨⟨realized_atomBlock L H,
      realized_atom_maximal_of_small_cover L H hH hcover⟩,
    by simpa using hH⟩

end AiMathLab.SaturatedSperner.ParameterizedAtom
