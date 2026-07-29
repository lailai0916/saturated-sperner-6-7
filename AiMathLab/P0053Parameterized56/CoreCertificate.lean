import AiMathLab.P0053Parameterized56.Templates

/-!
# Three-state core certificate for the parameterized 56 construction

An arbitrary external set is reduced symbolically to its seven-point core and
one of three atom states.  All bridges back to actual subsets are proved
before the fixed `7 * 128 * 3` table is checked by kernel `decide`.
-/

universe v

namespace AiMathLab.P0053Parameterized56

open AiMathLab.SaturatedSperner

/-- Projection of an arbitrary subset onto the seven fixed core points. -/
def coreProjection
    {H : Type v} [DecidableEq H]
    (S : Finset (ParamGround H)) : Finset (Fin 7) :=
  Finset.univ.filter fun i => Sum.inl i ∈ S

/-- Projection of an arbitrary subset onto the parameter atom. -/
def atomProjection
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) : Finset H :=
  Finset.univ.filter fun h => Sum.inr h ∈ S

/-- The exact three atom states needed for comparisons with all-or-none
templates. -/
inductive AtomState where
  | EMPTY
  | PARTIAL
  | FULL
deriving DecidableEq

instance : Fintype AtomState :=
  ⟨{.EMPTY, .PARTIAL, .FULL}, by
    intro q
    cases q <;> simp⟩

/-- Classify an atom projection, checking `EMPTY` before `FULL`. -/
def atomState
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) : AtomState :=
  if atomProjection S = ∅ then
    .EMPTY
  else if atomProjection S = Finset.univ then
    .FULL
  else
    .PARTIAL

/-- The finite signature seen by every source template. -/
structure CoreSignature where
  core : Finset (Fin 7)
  state : AtomState
deriving DecidableEq

/-- The signature of an actual subset. -/
def coreSignature
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) : CoreSignature :=
  ⟨coreProjection S, atomState S⟩

@[simp] theorem coreSignature_core
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    (coreSignature S).core = coreProjection S := rfl

@[simp] theorem coreSignature_state
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    (coreSignature S).state = atomState S := rfl

@[simp] theorem mem_coreProjection_iff
    {H : Type v} [DecidableEq H]
    (i : Fin 7) (S : Finset (ParamGround H)) :
    i ∈ coreProjection S ↔ Sum.inl i ∈ S := by
  simp [coreProjection]

@[simp] theorem mem_atomProjection_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (h : H) (S : Finset (ParamGround H)) :
    h ∈ atomProjection S ↔ Sum.inr h ∈ S := by
  simp [atomProjection]

theorem atomState_eq_EMPTY_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    atomState S = .EMPTY ↔ atomProjection S = ∅ := by
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

theorem atomState_eq_PARTIAL_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    atomState S = .PARTIAL ↔
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

theorem atomState_eq_FULL_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) :
    atomState S = .FULL ↔ atomProjection S = Finset.univ := by
  letI : Nonempty H := nonempty_of_vor hH
  let h0 : H := Classical.choice inferInstance
  have huniv : (Finset.univ : Finset H) ≠ ∅ := by
    intro heq
    have hh : h0 ∈ (Finset.univ : Finset H) := Finset.mem_univ h0
    rw [heq] at hh
    simpa using hh
  unfold atomState
  by_cases hE : atomProjection S = ∅
  · rw [if_pos hE]
    have hF : atomProjection S ≠ Finset.univ := by
      intro hEq
      exact huniv (hEq.symm.trans hE)
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

theorem atomState_exhaustive
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    atomState S = .EMPTY ∨ atomState S = .PARTIAL ∨
      atomState S = .FULL := by
  cases h : atomState S <;> simp [h]

theorem atomState_exclusive
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    (atomState S = .EMPTY → atomState S ≠ .PARTIAL) ∧
    (atomState S = .EMPTY → atomState S ≠ .FULL) ∧
    (atomState S = .PARTIAL → atomState S ≠ .FULL) := by
  constructor
  · intro hE hP
    cases hE.symm.trans hP
  constructor
  · intro hE hF
    cases hE.symm.trans hF
  · intro hP hF
    cases hP.symm.trans hF

theorem atomProjection_eq_empty_iff_disjoint
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    atomProjection S = ∅ ↔ Disjoint S (embeddedAtom H) := by
  constructor
  · intro hp
    rw [Finset.disjoint_left]
    intro x hxS hxH
    cases x with
    | inl i => exact inl_not_mem_embeddedAtom H i hxH
    | inr h =>
        have hh : h ∈ atomProjection S :=
          (mem_atomProjection_iff h S).mpr hxS
        simpa [hp] using hh
  · intro hdisj
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro h hh
    exact Finset.disjoint_left.mp hdisj
      ((mem_atomProjection_iff h S).mp hh)
      (inr_mem_embeddedAtom H h)

theorem atomProjection_eq_univ_iff_atom_subset
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    atomProjection S = Finset.univ ↔ embeddedAtom H ⊆ S := by
  constructor
  · intro hp x hx
    cases x with
    | inl i => exact False.elim (inl_not_mem_embeddedAtom H i hx)
    | inr h =>
        apply (mem_atomProjection_iff h S).mp
        rw [hp]
        exact Finset.mem_univ h
  · intro hsub
    ext h
    simp only [Finset.mem_univ, iff_true]
    exact (mem_atomProjection_iff h S).mpr
      (hsub (inr_mem_embeddedAtom H h))

theorem atomState_EMPTY_iff_disjoint
    {H : Type v} [Fintype H] [DecidableEq H]
    (S : Finset (ParamGround H)) :
    atomState S = .EMPTY ↔ Disjoint S (embeddedAtom H) := by
  rw [atomState_eq_EMPTY_iff, atomProjection_eq_empty_iff_disjoint]

theorem atomState_FULL_iff_atom_subset
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) :
    atomState S = .FULL ↔ embeddedAtom H ⊆ S := by
  rw [atomState_eq_FULL_iff hH,
    atomProjection_eq_univ_iff_atom_subset]

theorem atomState_PARTIAL_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) :
    atomState S = .PARTIAL ↔
      ¬ Disjoint S (embeddedAtom H) ∧
      ¬ embeddedAtom H ⊆ S := by
  rw [atomState_eq_PARTIAL_iff]
  exact and_congr
    (not_congr (atomProjection_eq_empty_iff_disjoint S))
    (not_congr (atomProjection_eq_univ_iff_atom_subset S))

/-- The state of a realized small or large template. -/
def expectedAtomState : AtomUse → AtomState
  | .small => .EMPTY
  | .large => .FULL

theorem coreProjection_realizeTemplate
    {H : Type v} [Fintype H] [DecidableEq H]
    (t : Template) :
    coreProjection (realizeTemplate H t) = t.core := by
  ext i
  simp

theorem atomProjection_realizeTemplate_small
    {H : Type v} [Fintype H] [DecidableEq H]
    (C : Finset (Fin 7)) :
    atomProjection (realizeTemplate H ⟨C, .small⟩) = ∅ := by
  ext h
  simp

theorem atomProjection_realizeTemplate_large
    {H : Type v} [Fintype H] [DecidableEq H]
    (C : Finset (Fin 7)) :
    atomProjection (realizeTemplate H ⟨C, .large⟩) = Finset.univ := by
  ext h
  simp

theorem atomState_realizeTemplate
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (t : Template) :
    atomState (realizeTemplate H t) =
      expectedAtomState t.atomUse := by
  cases t with
  | mk C use =>
      cases use with
      | small =>
          exact (atomState_eq_EMPTY_iff _).mpr
            (atomProjection_realizeTemplate_small C)
      | large =>
          exact (atomState_eq_FULL_iff hH _).mpr
            (atomProjection_realizeTemplate_large C)

/-- Whether an arbitrary atom state lies below a template atom flag. -/
def atomSubsetTemplate : AtomState → AtomUse → Prop
  | .EMPTY, .small => True
  | .PARTIAL, .small => False
  | .FULL, .small => False
  | _, .large => True

/-- Whether a template atom flag lies below an arbitrary atom state. -/
def templateAtomSubset : AtomUse → AtomState → Prop
  | .small, _ => True
  | .large, .FULL => True
  | .large, .EMPTY => False
  | .large, .PARTIAL => False

/-- Equality of a finite signature with a template. -/
def signatureEqTemplate (σ : CoreSignature) (t : Template) : Prop :=
  σ.core = t.core ∧ σ.state = expectedAtomState t.atomUse

/-- Signature subset of a template. -/
def signatureSubsetTemplate (σ : CoreSignature) (t : Template) : Prop :=
  σ.core ⊆ t.core ∧ atomSubsetTemplate σ.state t.atomUse

/-- Template subset of a signature. -/
def templateSubsetSignature (t : Template) (σ : CoreSignature) : Prop :=
  t.core ⊆ σ.core ∧ templateAtomSubset t.atomUse σ.state

/-- Strict signature subset of a template. -/
def signatureStrictSubsetTemplate
    (σ : CoreSignature) (t : Template) : Prop :=
  signatureSubsetTemplate σ t ∧ ¬ signatureEqTemplate σ t

/-- Strict template subset of a signature. -/
def templateStrictSubsetSignature
    (t : Template) (σ : CoreSignature) : Prop :=
  templateSubsetSignature t σ ∧ ¬ signatureEqTemplate σ t

/-- Strict comparability of a signature and a template. -/
def signatureComparable (σ : CoreSignature) (t : Template) : Prop :=
  signatureStrictSubsetTemplate σ t ∨
    templateStrictSubsetSignature t σ

/-- Exact signature membership in one source layer. -/
def signatureMember (i : Fin 7) (σ : CoreSignature) : Prop :=
  ∃ t ∈ templateLayer i, signatureEqTemplate σ t

/-- Strict signature comparability with some template in one source layer. -/
def signatureComparableInLayer (i : Fin 7) (σ : CoreSignature) : Prop :=
  ∃ t ∈ templateLayer i, signatureComparable σ t

instance instDecidableAtomSubsetTemplate (q : AtomState) (u : AtomUse) :
    Decidable (atomSubsetTemplate q u) := by
  cases q <;> cases u
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id
  · exact isTrue trivial
  · exact isFalse id
  · exact isTrue trivial

instance instDecidableTemplateAtomSubset (u : AtomUse) (q : AtomState) :
    Decidable (templateAtomSubset u q) := by
  cases u <;> cases q
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id
  · exact isFalse id
  · exact isTrue trivial

instance instDecidableSignatureEqTemplate
    (σ : CoreSignature) (t : Template) :
    Decidable (signatureEqTemplate σ t) := by
  unfold signatureEqTemplate
  infer_instance

instance instDecidableSignatureSubsetTemplate
    (σ : CoreSignature) (t : Template) :
    Decidable (signatureSubsetTemplate σ t) := by
  unfold signatureSubsetTemplate
  infer_instance

instance instDecidableTemplateSubsetSignature
    (t : Template) (σ : CoreSignature) :
    Decidable (templateSubsetSignature t σ) := by
  unfold templateSubsetSignature
  infer_instance

instance instDecidableSignatureStrictSubsetTemplate
    (σ : CoreSignature) (t : Template) :
    Decidable (signatureStrictSubsetTemplate σ t) := by
  unfold signatureStrictSubsetTemplate
  infer_instance

instance instDecidableTemplateStrictSubsetSignature
    (t : Template) (σ : CoreSignature) :
    Decidable (templateStrictSubsetSignature t σ) := by
  unfold templateStrictSubsetSignature
  infer_instance

instance instDecidableSignatureComparable
    (σ : CoreSignature) (t : Template) :
    Decidable (signatureComparable σ t) := by
  unfold signatureComparable
  infer_instance

instance instDecidableSignatureMember (i : Fin 7) (σ : CoreSignature) :
    Decidable (signatureMember i σ) := by
  unfold signatureMember
  infer_instance

instance instDecidableSignatureComparableInLayer
    (i : Fin 7) (σ : CoreSignature) :
    Decidable (signatureComparableInLayer i σ) := by
  unfold signatureComparableInLayer
  infer_instance

theorem eq_realizeTemplate_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) (t : Template) :
    S = realizeTemplate H t ↔
      signatureEqTemplate (coreSignature S) t := by
  constructor
  · rintro rfl
    exact ⟨coreProjection_realizeTemplate t,
      atomState_realizeTemplate hH t⟩
  · rintro ⟨hcore, hstate⟩
    change coreProjection S = t.core at hcore
    change atomState S = expectedAtomState t.atomUse at hstate
    ext x
    cases x with
    | inl i =>
        rw [inl_mem_realizeTemplate_iff,
          ← mem_coreProjection_iff]
        exact Finset.ext_iff.mp hcore i
    | inr h =>
        rw [inr_mem_realizeTemplate_iff]
        cases hu : t.atomUse with
        | small =>
            have hsE : atomState S = .EMPTY := by
              simpa [expectedAtomState, hu] using hstate
            have hp := (atomState_eq_EMPTY_iff S).mp hsE
            constructor
            · intro hx
              have hh := (mem_atomProjection_iff h S).mpr hx
              simpa [hp] using hh
            · simp [hu]
        | large =>
            have hsF : atomState S = .FULL := by
              simpa [expectedAtomState, hu] using hstate
            have hp := (atomState_eq_FULL_iff hH S).mp hsF
            constructor
            · intro _
              rfl
            · intro _
              apply (mem_atomProjection_iff h S).mp
              rw [hp]
              exact Finset.mem_univ h

theorem subset_realizeTemplate_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) (t : Template) :
    S ⊆ realizeTemplate H t ↔
      signatureSubsetTemplate (coreSignature S) t := by
  constructor
  · intro hsub
    refine ⟨?_, ?_⟩
    · intro i hi
      apply (inl_mem_realizeTemplate_iff H i t).mp
      exact hsub ((mem_coreProjection_iff i S).mp hi)
    · change atomSubsetTemplate (atomState S) t.atomUse
      cases hs : atomState S <;> cases hu : t.atomUse
      · simp [atomSubsetTemplate, hs, hu]
      · simp [atomSubsetTemplate, hs, hu]
      · exfalso
        have hpne : atomProjection S ≠ ∅ :=
          (atomState_eq_PARTIAL_iff S).mp hs |>.1
        rcases Finset.nonempty_iff_ne_empty.mpr hpne with ⟨h, hh⟩
        have hx := hsub ((mem_atomProjection_iff h S).mp hh)
        simpa [hu] using hx
      · simp [atomSubsetTemplate, hs, hu]
      · exfalso
        let h0 : H := Classical.choice (nonempty_of_vor hH)
        have hp := (atomState_eq_FULL_iff hH S).mp hs
        have hh : h0 ∈ atomProjection S := by simp [hp]
        have hx := hsub ((mem_atomProjection_iff h0 S).mp hh)
        simpa [hu] using hx
      · simp [atomSubsetTemplate, hs, hu]
  · rintro ⟨hcore, hatom⟩ x hx
    change coreProjection S ⊆ t.core at hcore
    change atomSubsetTemplate (atomState S) t.atomUse at hatom
    cases x with
    | inl i =>
        apply (inl_mem_realizeTemplate_iff H i t).mpr
        exact hcore ((mem_coreProjection_iff i S).mpr hx)
    | inr h =>
        cases hs : atomState S <;> cases hu : t.atomUse
        · have hp := (atomState_eq_EMPTY_iff S).mp hs
          have hh := (mem_atomProjection_iff h S).mpr hx
          simpa [hp] using hh
        · exact (inr_mem_realizeTemplate_iff H h t).mpr hu
        · simp [atomSubsetTemplate, hs, hu] at hatom
        · exact (inr_mem_realizeTemplate_iff H h t).mpr hu
        · simp [atomSubsetTemplate, hs, hu] at hatom
        · exact (inr_mem_realizeTemplate_iff H h t).mpr hu

theorem realizeTemplate_subset_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) (t : Template) :
    realizeTemplate H t ⊆ S ↔
      templateSubsetSignature t (coreSignature S) := by
  constructor
  · intro hsub
    refine ⟨?_, ?_⟩
    · intro i hi
      apply (mem_coreProjection_iff i S).mpr
      exact hsub ((inl_mem_realizeTemplate_iff H i t).mpr hi)
    · change templateAtomSubset t.atomUse (atomState S)
      cases hu : t.atomUse <;> cases hs : atomState S
      · simp [templateAtomSubset, hu, hs]
      · simp [templateAtomSubset, hu, hs]
      · simp [templateAtomSubset, hu, hs]
      · exfalso
        let h0 : H := Classical.choice (nonempty_of_vor hH)
        have hx := hsub ((inr_mem_realizeTemplate_iff H h0 t).mpr hu)
        have hh := (mem_atomProjection_iff h0 S).mpr hx
        have hp := (atomState_eq_EMPTY_iff S).mp hs
        simpa [hp] using hh
      · exfalso
        have hpnot : atomProjection S ≠ Finset.univ :=
          (atomState_eq_PARTIAL_iff S).mp hs |>.2
        apply hpnot
        ext h
        simp only [Finset.mem_univ, iff_true]
        exact (mem_atomProjection_iff h S).mpr
          (hsub ((inr_mem_realizeTemplate_iff H h t).mpr hu))
      · simp [templateAtomSubset, hu, hs]
  · rintro ⟨hcore, hatom⟩ x hx
    change t.core ⊆ coreProjection S at hcore
    change templateAtomSubset t.atomUse (atomState S) at hatom
    cases x with
    | inl i =>
        apply (mem_coreProjection_iff i S).mp
        exact hcore ((inl_mem_realizeTemplate_iff H i t).mp hx)
    | inr h =>
        have htlarge := (inr_mem_realizeTemplate_iff H h t).mp hx
        cases hu : t.atomUse <;> cases hs : atomState S
        · simp [hu] at htlarge
        · simp [hu] at htlarge
        · simp [hu] at htlarge
        · simp [templateAtomSubset, hu, hs] at hatom
        · simp [templateAtomSubset, hu, hs] at hatom
        · have hp := (atomState_eq_FULL_iff hH S).mp hs
          apply (mem_atomProjection_iff h S).mp
          rw [hp]
          exact Finset.mem_univ h

theorem ssubset_realizeTemplate_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) (t : Template) :
    S ⊂ realizeTemplate H t ↔
      signatureStrictSubsetTemplate (coreSignature S) t := by
  rw [ssubset_iff_subset_ne, signatureStrictSubsetTemplate,
    subset_realizeTemplate_iff hH]
  exact and_congr_right fun _ =>
    not_congr (eq_realizeTemplate_iff hH S t)

theorem realizeTemplate_ssubset_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) (t : Template) :
    realizeTemplate H t ⊂ S ↔
      templateStrictSubsetSignature t (coreSignature S) := by
  rw [ssubset_iff_subset_ne, templateStrictSubsetSignature,
    realizeTemplate_subset_iff hH]
  have heq :
      realizeTemplate H t = S ↔
        signatureEqTemplate (coreSignature S) t := by
    constructor
    · intro hEq
      exact (eq_realizeTemplate_iff hH S t).mp hEq.symm
    · intro hsig
      exact ((eq_realizeTemplate_iff hH S t).mpr hsig).symm
  exact and_congr_right fun _ => not_congr heq

theorem strictComparable_realizeTemplate_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (S : Finset (ParamGround H)) (t : Template) :
    (S ⊂ realizeTemplate H t ∨ realizeTemplate H t ⊂ S) ↔
      signatureComparable (coreSignature S) t := by
  rw [signatureComparable, ssubset_realizeTemplate_iff hH,
    realizeTemplate_ssubset_iff hH]

theorem mem_parameterized56Layers_iff
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H)
    (i : Fin 7) (S : Finset (ParamGround H)) :
    S ∈ parameterized56Layers H i ↔
      signatureMember i (coreSignature S) := by
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨t, ht, hreal⟩
    refine ⟨t, ht, (eq_realizeTemplate_iff hH S t).mp ?_⟩
    exact hreal.symm
  · rintro ⟨t, ht, hsig⟩
    exact Finset.mem_image.mpr
      ⟨t, ht, ((eq_realizeTemplate_iff hH S t).mpr hsig).symm⟩

/-- Each closed cell is either an exact member with no same-layer strict
comparison, or an external signature with a strict comparison witness. -/
def CoreCellResolved (i : Fin 7) (σ : CoreSignature) : Prop :=
  (signatureMember i σ ∧
      ∀ t ∈ templateLayer i, ¬ signatureComparable σ t) ∨
  (¬ signatureMember i σ ∧
      ∃ t ∈ templateLayer i, signatureComparable σ t)

instance instDecidableCoreCellResolved (i : Fin 7) (σ : CoreSignature) :
    Decidable (CoreCellResolved i σ) := by
  unfold CoreCellResolved
  infer_instance

/-- The full fixed certificate proposition. -/
def CoreCertificate : Prop :=
  ∀ (i : Fin 7) (C : Finset (Fin 7)) (q : AtomState),
    CoreCellResolved i ⟨C, q⟩

set_option maxRecDepth 100000 in
private theorem coreCertificate_layer0 :
    ∀ C q, CoreCellResolved 0 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem coreCertificate_layer1 :
    ∀ C q, CoreCellResolved 1 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem coreCertificate_layer2 :
    ∀ C q, CoreCellResolved 2 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem coreCertificate_layer3 :
    ∀ C q, CoreCellResolved 3 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem coreCertificate_layer4 :
    ∀ C q, CoreCellResolved 4 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem coreCertificate_layer5 :
    ∀ C q, CoreCellResolved 5 ⟨C, q⟩ := by
  decide

set_option maxRecDepth 100000 in
private theorem coreCertificate_layer6 :
    ∀ C q, CoreCellResolved 6 ⟨C, q⟩ := by
  decide

/-- Kernel-checked soundness of all 2688 fixed core/state cells. -/
theorem coreCertificate_sound : CoreCertificate := by
  intro i
  fin_cases i
  · exact coreCertificate_layer0
  · exact coreCertificate_layer1
  · exact coreCertificate_layer2
  · exact coreCertificate_layer3
  · exact coreCertificate_layer4
  · exact coreCertificate_layer5
  · exact coreCertificate_layer6

set_option maxRecDepth 100000 in
theorem coreCertificate_domain_card :
    Fintype.card (Fin 7 × (Finset (Fin 7) × AtomState)) = 2688 := by
  decide

theorem isSaturatedKSperner_one_of_comparable
    {α : Type*} [DecidableEq α]
    {F : Family α}
    (hanti : ∀ A ∈ F, ∀ B ∈ F, ¬ A ⊂ B)
    (hext : ∀ S : Finset α, S ∉ F →
      ∃ T ∈ F, T ⊂ S ∨ S ⊂ T) :
    IsSaturatedKSperner 1 F := by
  refine ⟨?_, ?_⟩
  · rintro ⟨B, hBF, A, hAF, hAB⟩
    exact hanti A hAF B hBF hAB
  · intro S hSF
    rcases hext S hSF with ⟨T, hTF, hTS | hST⟩
    · exact ⟨S, Finset.mem_insert_self S F,
        T, Finset.mem_insert_of_mem hTF, hTS⟩
    · exact ⟨T, Finset.mem_insert_of_mem hTF,
        S, Finset.mem_insert_self S F, hST⟩

theorem parameterized56Layer_no_ssubset
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (i : Fin 7)
    {A B : Finset (ParamGround H)}
    (hA : A ∈ parameterized56Layers H i)
    (hB : B ∈ parameterized56Layers H i) :
    ¬ A ⊂ B := by
  intro hAB
  have hAsig := (mem_parameterized56Layers_iff hH i A).mp hA
  have hcell := coreCertificate_sound i (coreProjection A) (atomState A)
  change CoreCellResolved i (coreSignature A) at hcell
  rcases hcell with hmember | hexternal
  · rcases Finset.mem_image.mp hB with ⟨t, ht, hreal⟩
    apply hmember.2 t ht
    apply (strictComparable_realizeTemplate_iff hH A t).mp
    exact Or.inl (by simpa [hreal] using hAB)
  · exact False.elim (hexternal.1 hAsig)

theorem parameterized56Layer_external_comparable
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (i : Fin 7)
    {S : Finset (ParamGround H)}
    (hS : S ∉ parameterized56Layers H i) :
    ∃ T ∈ parameterized56Layers H i, T ⊂ S ∨ S ⊂ T := by
  have hSsig : ¬ signatureMember i (coreSignature S) := by
    exact fun hs => hS ((mem_parameterized56Layers_iff hH i S).mpr hs)
  have hcell := coreCertificate_sound i (coreProjection S) (atomState S)
  change CoreCellResolved i (coreSignature S) at hcell
  rcases hcell with hmember | hexternal
  · exact False.elim (hSsig hmember.1)
  · rcases hexternal.2 with ⟨t, ht, hcomp⟩
    have hactual :=
      (strictComparable_realizeTemplate_iff hH S t).mpr hcomp
    refine ⟨realizeTemplate H t,
      Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    exact hactual.symm

theorem parameterized56_layer_saturated
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) (i : Fin 7) :
    IsSaturatedKSperner 1 (parameterized56Layers H i) := by
  apply isSaturatedKSperner_one_of_comparable
  · intro A hA B hB
    exact parameterized56Layer_no_ssubset hH i hA hB
  · intro S hS
    exact parameterized56Layer_external_comparable hH i hS

/-- Every realized source layer is a saturated antichain for every legal
parameter atom, including against partial-atom external subsets. -/
theorem parameterized56_layers_saturated
    {H : Type v} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    ∀ i : Fin 7,
      IsSaturatedKSperner 1 (parameterized56Layers H i) := by
  intro i
  exact parameterized56_layer_saturated hH i

end AiMathLab.P0053Parameterized56
