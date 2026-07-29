import AiMathLab.SaturatedSperner.Composition
import AiMathLab.SaturatedSperner.StandardConstruction
import AiMathLab.P0053Parameterized56

/-!
# The exact P0053 composition upper bound

This module first reads the small/large split directly from the accepted F3C
template flags.  It then iterates a genuine `Fin 3` parameterized factor and
composes it with the symbolic standard construction.  Finally, it transports
the result to `Fin n` for every ground size above an explicit threshold.
-/

universe u

namespace AiMathLab.P0053Parameterized56

open AiMathLab.SaturatedSperner

/-- The ordered source rows whose atom flag is small. -/
def smallTemplateTable : List Template :=
  templateTable.filter fun t => t.atomUse == .small

/-- The ordered source rows whose atom flag is large. -/
def largeTemplateTable : List Template :=
  templateTable.filter fun t => t.atomUse == .large

/-- The set of small-flag source templates. -/
def smallTemplates : Finset Template :=
  smallTemplateTable.toFinset

/-- The set of large-flag source templates. -/
def largeTemplates : Finset Template :=
  largeTemplateTable.toFinset

/-- Direct closed reduction of the frozen small flags. -/
theorem smallTemplateTable_length : smallTemplateTable.length = 28 := by
  rfl

/-- Direct closed reduction of the frozen large flags. -/
theorem largeTemplateTable_length : largeTemplateTable.length = 28 := by
  rfl

theorem smallTemplateTable_nodup : smallTemplateTable.Nodup := by
  exact templateTable_nodup.filter _

theorem largeTemplateTable_nodup : largeTemplateTable.Nodup := by
  exact templateTable_nodup.filter _

/-- Exactly 28 frozen rows carry the small flag. -/
theorem smallTemplates_card : smallTemplates.card = 28 := by
  rw [smallTemplates,
    List.toFinset_card_of_nodup smallTemplateTable_nodup]
  exact smallTemplateTable_length

/-- Exactly 28 frozen rows carry the large flag. -/
theorem largeTemplates_card : largeTemplates.card = 28 := by
  rw [largeTemplates,
    List.toFinset_card_of_nodup largeTemplateTable_nodup]
  exact largeTemplateTable_length

@[simp] theorem mem_smallTemplates_iff {t : Template} :
    t ∈ smallTemplates ↔ t ∈ templateUnion ∧ t.atomUse = .small := by
  simp [smallTemplates, smallTemplateTable, templateUnion]

@[simp] theorem mem_largeTemplates_iff {t : Template} :
    t ∈ largeTemplates ↔ t ∈ templateUnion ∧ t.atomUse = .large := by
  simp [largeTemplates, largeTemplateTable, templateUnion]

/-- Readback of the exact homogeneous small part through realization. -/
theorem parameterized56_smallPart_eq_image
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    SmallPart (parameterized56 H) (embeddedAtom H) =
      smallTemplates.image (realizeTemplate H) := by
  ext S
  constructor
  · intro hS
    rcases mem_smallPart.mp hS with ⟨hSF, hdisj⟩
    rw [parameterized56_eq_image_templateUnion] at hSF
    rcases Finset.mem_image.mp hSF with ⟨t, ht, htS⟩
    have huse : t.atomUse = .small := by
      cases hu : t.atomUse with
      | small => exact rfl
      | large =>
          let h0 : H := Classical.choice (nonempty_of_vor hH)
          have hhReal : Sum.inr h0 ∈ realizeTemplate H t :=
            (inr_mem_realizeTemplate_iff H h0 t).mpr hu
          have hhS : Sum.inr h0 ∈ S := by rw [← htS]; exact hhReal
          exact False.elim ((Finset.disjoint_left.mp hdisj) hhS
            (inr_mem_embeddedAtom H h0))
    exact Finset.mem_image.mpr
      ⟨t, mem_smallTemplates_iff.mpr ⟨ht, huse⟩, htS⟩
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨t, ht, htS⟩
    have htUnion := (mem_smallTemplates_iff.mp ht).1
    have htSmall := (mem_smallTemplates_iff.mp ht).2
    apply mem_smallPart.mpr
    constructor
    · rw [parameterized56_eq_image_templateUnion]
      exact Finset.mem_image.mpr ⟨t, htUnion, htS⟩
    · rw [Finset.disjoint_left]
      intro z hzS hzAtom
      have hzReal : z ∈ realizeTemplate H t := by rw [htS]; exact hzS
      cases z with
      | inl i => exact inl_not_mem_embeddedAtom H i hzAtom
      | inr h =>
          have := (inr_mem_realizeTemplate_iff H h t).mp hzReal
          rw [htSmall] at this
          cases this

/-- Readback of the exact homogeneous large part through realization. -/
theorem parameterized56_largePart_eq_image
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    LargePart (parameterized56 H) (embeddedAtom H) =
      largeTemplates.image (realizeTemplate H) := by
  ext S
  constructor
  · intro hS
    rcases mem_largePart.mp hS with ⟨hSF, hAtomSub⟩
    rw [parameterized56_eq_image_templateUnion] at hSF
    rcases Finset.mem_image.mp hSF with ⟨t, ht, htS⟩
    have huse : t.atomUse = .large := by
      cases hu : t.atomUse with
      | large => exact rfl
      | small =>
          let h0 : H := Classical.choice (nonempty_of_vor hH)
          have hhS : Sum.inr h0 ∈ S :=
            hAtomSub (inr_mem_embeddedAtom H h0)
          have hhReal : Sum.inr h0 ∈ realizeTemplate H t := by
            rw [htS]
            exact hhS
          have := (inr_mem_realizeTemplate_iff H h0 t).mp hhReal
          rw [hu] at this
          cases this
    exact Finset.mem_image.mpr
      ⟨t, mem_largeTemplates_iff.mpr ⟨ht, huse⟩, htS⟩
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨t, ht, htS⟩
    have htUnion := (mem_largeTemplates_iff.mp ht).1
    have htLarge := (mem_largeTemplates_iff.mp ht).2
    apply mem_largePart.mpr
    constructor
    · rw [parameterized56_eq_image_templateUnion]
      exact Finset.mem_image.mpr ⟨t, htUnion, htS⟩
    · intro z hzAtom
      cases z with
      | inl i => exact False.elim (inl_not_mem_embeddedAtom H i hzAtom)
      | inr h =>
          rw [← htS]
          exact (inr_mem_realizeTemplate_iff H h t).mpr htLarge

/-- The parameterized F3C small part has exact cardinality 28. -/
theorem parameterized56_small_card
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    (SmallPart (parameterized56 H) (embeddedAtom H)).card = 28 := by
  rw [parameterized56_smallPart_eq_image hH,
    Finset.card_image_of_injective _ (realizeTemplate_injective hH)]
  exact smallTemplates_card

/-- The parameterized F3C large part has exact cardinality 28. -/
theorem parameterized56_large_card
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    (LargePart (parameterized56 H) (embeddedAtom H)).card = 28 := by
  rw [parameterized56_largePart_eq_image hH,
    Finset.card_image_of_injective _ (realizeTemplate_injective hH)]
  exact largeTemplates_card

private theorem smallMask_zero_mem_templateUnion :
    smallMask 0 ∈ templateUnion := by
  simp [templateUnion, templateTable, sourceRows]

private theorem largeMask_top_mem_templateUnion :
    largeMask 127 ∈ templateUnion := by
  simp [templateUnion, templateTable, sourceRows]

private theorem realize_smallMask_zero
    (H : Type u) [Fintype H] [DecidableEq H] :
    realizeTemplate H (smallMask 0) = ∅ := by
  ext z
  cases z with
  | inl i =>
      fin_cases i <;>
        norm_num [realizeTemplate, smallMask, coreFromMask,
          embeddedCore, coreEmbedding]
  | inr h => simp [realizeTemplate, smallMask]

private theorem realize_largeMask_top
    (H : Type u) [Fintype H] [DecidableEq H] :
    realizeTemplate H (largeMask 127) = Finset.univ := by
  ext z
  cases z with
  | inl i =>
      fin_cases i <;>
        norm_num [realizeTemplate, largeMask, coreFromMask,
          embeddedCore, coreEmbedding] <;> rfl
  | inr h => simp [realizeTemplate, largeMask]

/-- The F3C factor contains its bottom and top sets, proved from the direct
bottom and top source rows. -/
theorem parameterized56_hasEndpoints
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    HasEndpoints (parameterized56 H) := by
  constructor
  · rw [parameterized56_eq_image_templateUnion]
    exact Finset.mem_image.mpr
      ⟨smallMask 0, smallMask_zero_mem_templateUnion,
        realize_smallMask_zero H⟩
  · rw [parameterized56_eq_image_templateUnion]
    exact Finset.mem_image.mpr
      ⟨largeMask 127, largeMask_top_mem_templateUnion,
        realize_largeMask_top H⟩

/-- The accepted F3C construction packaged as a composition factor. -/
theorem parameterized56_composition_factor
    {H : Type u} [Fintype H] [DecidableEq H]
    (hH : 2 < Fintype.card H) :
    IsSaturatedKSperner 7 (parameterized56 H) ∧
      HasEndpoints (parameterized56 H) ∧
      IsHomogeneousAtom (parameterized56 H) (embeddedAtom H) ∧
      (SmallPart (parameterized56 H) (embeddedAtom H)).card = 28 ∧
      (LargePart (parameterized56 H) (embeddedAtom H)).card = 28 := by
  exact ⟨parameterized56_saturated hH, parameterized56_hasEndpoints hH,
    parameterized56_homogeneousAtom hH,
    parameterized56_small_card hH, parameterized56_large_card hH⟩

end AiMathLab.P0053Parameterized56

namespace AiMathLab.P0053UpperBound

open AiMathLab.SaturatedSperner
open AiMathLab.P0053Parameterized56

/-- The genuine ten-point base ground, with the smallest legal atom. -/
abbrev FactorGround := ParamGround (Fin 3)

/-- The genuine parameterized F3C base factor. -/
def factorFamily : Family FactorGround :=
  parameterized56 (Fin 3)

/-- The homogeneous atom of the genuine base factor. -/
def factorAtom : Finset FactorGround :=
  embeddedAtom (Fin 3)

/-- Internal index `q` represents exactly `q + 1` genuine factors. -/
def IterGroundAux : Nat → Type
  | 0 => FactorGround
  | q + 1 => IterGroundAux q ⊕ FactorGround

instance iterGroundAuxDecidableEq :
    (q : Nat) → DecidableEq (IterGroundAux q)
  | 0 =>
      @instDecidableEqSum (Fin 7) (Fin 3) inferInstance inferInstance
  | q + 1 =>
      @instDecidableEqSum (IterGroundAux q) FactorGround
        (iterGroundAuxDecidableEq q) inferInstance

instance iterGroundAuxFintype : (q : Nat) → Fintype (IterGroundAux q)
  | 0 =>
      @instFintypeSum (Fin 7) (Fin 3) inferInstance inferInstance
  | q + 1 =>
      @instFintypeSum (IterGroundAux q) FactorGround
        (iterGroundAuxFintype q) inferInstance

/-- Recursive combined atom for `q + 1` genuine factors. -/
def iterated56AtomAux : (q : Nat) → Finset (IterGroundAux q)
  | 0 => factorAtom
  | q + 1 => sumSubset (iterated56AtomAux q) factorAtom

/-- Recursive family for `q + 1` genuine factors. -/
def iterated56Aux : (q : Nat) → Family (IterGroundAux q)
  | 0 => factorFamily
  | q + 1 =>
      composeFamilies
        (iterated56Aux q) (iterated56AtomAux q)
        factorFamily factorAtom

private theorem factor_atom_legal :
    2 < Fintype.card (Fin 3) := by
  simp

private theorem factor_saturated :
    IsSaturatedKSperner 7 factorFamily := by
  simpa [factorFamily] using
    parameterized56_saturated (H := Fin 3) factor_atom_legal

private theorem factor_endpoints : HasEndpoints factorFamily := by
  simpa [factorFamily] using
    parameterized56_hasEndpoints (H := Fin 3) factor_atom_legal

private theorem factor_homogeneousAtom :
    IsHomogeneousAtom factorFamily factorAtom := by
  simpa [factorFamily, factorAtom] using
    parameterized56_homogeneousAtom (H := Fin 3) factor_atom_legal

private theorem factor_small_card :
    (SmallPart factorFamily factorAtom).card = 28 := by
  simpa [factorFamily, factorAtom] using
    parameterized56_small_card (H := Fin 3) factor_atom_legal

private theorem factor_large_card :
    (LargePart factorFamily factorAtom).card = 28 := by
  simpa [factorFamily, factorAtom] using
    parameterized56_large_card (H := Fin 3) factor_atom_legal

private theorem family_card_eq_parts
    {α : Type u} [DecidableEq α]
    {F : Family α} {H : Finset α}
    (hblock : IsAtomBlock F H) (hH : H.Nonempty) :
    F.card = (SmallPart F H).card + (LargePart F H).card := by
  have hcover := atomBlock_small_large_cover hblock
  calc
    F.card = (SmallPart F H ∪ LargePart F H).card := by rw [hcover]
    _ = (SmallPart F H).card + (LargePart F H).card :=
      Finset.card_union_of_disjoint (smallPart_largePart_disjoint hH)

/-- The simultaneous induction invariant for the genuine-factor recursion. -/
structure Iterated56AuxInvariant (q : Nat) : Prop where
  ground_card : Fintype.card (IterGroundAux q) = 10 * (q + 1)
  saturated :
    IsSaturatedKSperner (5 * (q + 1) + 2) (iterated56Aux q)
  endpoints : HasEndpoints (iterated56Aux q)
  homogeneousAtom :
    IsHomogeneousAtom (iterated56Aux q) (iterated56AtomAux q)
  small_card :
    (SmallPart (iterated56Aux q) (iterated56AtomAux q)).card =
      28 ^ (q + 1)
  large_card :
    (LargePart (iterated56Aux q) (iterated56AtomAux q)).card =
      28 ^ (q + 1)
  total_card : (iterated56Aux q).card = 2 * 28 ^ (q + 1)

/-- One induction proves the parameter, endpoints, atom, both exact parts,
total cardinality, and ground cardinality together. -/
theorem iterated56Aux_invariant :
    ∀ q : Nat, Iterated56AuxInvariant q
  | 0 => by
      have hhom :
          IsHomogeneousAtom (iterated56Aux 0) (iterated56AtomAux 0) := by
        simpa [iterated56Aux, iterated56AtomAux, IterGroundAux,
          iterGroundAuxDecidableEq]
          using factor_homogeneousAtom
      have hsmall :
          (SmallPart (iterated56Aux 0) (iterated56AtomAux 0)).card =
            28 ^ (0 + 1) := by
        change (@SmallPart FactorGround (iterGroundAuxDecidableEq 0)
          factorFamily factorAtom).card = 28
        have hde : iterGroundAuxDecidableEq 0 =
            (inferInstance : DecidableEq FactorGround) :=
          Subsingleton.elim _ _
        rw [hde]
        exact factor_small_card
      have hlarge :
          (LargePart (iterated56Aux 0) (iterated56AtomAux 0)).card =
            28 ^ (0 + 1) := by
        change (@LargePart FactorGround (iterGroundAuxDecidableEq 0)
          factorFamily factorAtom).card = 28
        have hde : iterGroundAuxDecidableEq 0 =
            (inferInstance : DecidableEq FactorGround) :=
          Subsingleton.elim _ _
        rw [hde]
        exact factor_large_card
      have htotal := family_card_eq_parts hhom.1.1
        (Finset.card_pos.mp (by have := hhom.2; omega))
      refine ⟨?_, ?_, ?_, hhom, hsmall, hlarge, ?_⟩
      · change Fintype.card (Fin 7 ⊕ Fin 3) = 10
        rw [Fintype.card_sum]
        simp
      · simpa [iterated56Aux, IterGroundAux,
          iterGroundAuxDecidableEq, factorFamily]
          using factor_saturated
      · simpa [iterated56Aux, IterGroundAux,
          iterGroundAuxFintype, factorFamily]
          using factor_endpoints
      · rw [hsmall, hlarge] at htotal
        simpa using htotal
  | q + 1 => by
      have ih := iterated56Aux_invariant q
      have hprevAtom : (iterated56AtomAux q).Nonempty :=
        Finset.card_pos.mp (by have := ih.homogeneousAtom.2; omega)
      have hfactorAtom : factorAtom.Nonempty :=
        Finset.card_pos.mp (by
          have := factor_homogeneousAtom.2
          omega)
      have hde : iterGroundAuxDecidableEq (q + 1) =
          @instDecidableEqSum (IterGroundAux q) FactorGround
            (iterGroundAuxDecidableEq q)
            (inferInstance : DecidableEq FactorGround) :=
        Subsingleton.elim _ _
      have hsaturated :
          IsSaturatedKSperner (5 * ((q + 1) + 1) + 2)
            (iterated56Aux (q + 1)) := by
        have hcompose := compose_saturated
          ih.saturated factor_saturated ih.endpoints factor_endpoints
          ih.homogeneousAtom factor_homogeneousAtom
        change IsSaturatedKSperner (5 * ((q + 1) + 1) + 2)
          (composeFamilies (iterated56Aux q) (iterated56AtomAux q)
            factorFamily factorAtom)
        convert hcompose using 1 <;> omega
      have hendpoints : HasEndpoints (iterated56Aux (q + 1)) := by
        simpa [iterated56Aux, IterGroundAux, iterGroundAuxFintype] using
          compose_hasEndpoints ih.endpoints factor_endpoints
      have hhomogeneous :
          IsHomogeneousAtom (iterated56Aux (q + 1))
            (iterated56AtomAux (q + 1)) := by
        simpa [iterated56Aux, iterated56AtomAux, IterGroundAux] using
          compose_homogeneousAtom ih.endpoints factor_endpoints
            ih.homogeneousAtom factor_homogeneousAtom
      have hsmallCompose := compose_small_card
        (F₁ := iterated56Aux q) (H₁ := iterated56AtomAux q)
        (F₂ := factorFamily) (H₂ := factorAtom)
        hprevAtom hfactorAtom
      have hsmall :
          (SmallPart (iterated56Aux (q + 1))
            (iterated56AtomAux (q + 1))).card = 28 ^ ((q + 1) + 1) := by
        change (@SmallPart (IterGroundAux q ⊕ FactorGround)
          (iterGroundAuxDecidableEq (q + 1))
          (composeFamilies (iterated56Aux q) (iterated56AtomAux q)
            factorFamily factorAtom)
          (sumSubset (iterated56AtomAux q) factorAtom)).card =
            28 ^ ((q + 1) + 1)
        rw [hde]
        rw [ih.small_card, factor_small_card] at hsmallCompose
        simpa [pow_succ] using hsmallCompose
      have hlargeCompose := compose_large_card
        (F₁ := iterated56Aux q) (H₁ := iterated56AtomAux q)
        (F₂ := factorFamily) (H₂ := factorAtom)
        hprevAtom hfactorAtom
      have hlarge :
          (LargePart (iterated56Aux (q + 1))
            (iterated56AtomAux (q + 1))).card = 28 ^ ((q + 1) + 1) := by
        change (@LargePart (IterGroundAux q ⊕ FactorGround)
          (iterGroundAuxDecidableEq (q + 1))
          (composeFamilies (iterated56Aux q) (iterated56AtomAux q)
            factorFamily factorAtom)
          (sumSubset (iterated56AtomAux q) factorAtom)).card =
            28 ^ ((q + 1) + 1)
        rw [hde]
        rw [ih.large_card, factor_large_card] at hlargeCompose
        simpa [pow_succ] using hlargeCompose
      have htotal := family_card_eq_parts hhomogeneous.1.1
        (Finset.card_pos.mp (by have := hhomogeneous.2; omega))
      refine ⟨?_, hsaturated, hendpoints, hhomogeneous,
        hsmall, hlarge, ?_⟩
      · simp only [IterGroundAux, Fintype.card_sum]
        rw [ih.ground_card]
        simp [FactorGround, ParamGround]
        omega
      · rw [hsmall, hlarge] at htotal
        omega

/-- Public ground for `j` factors.  Theorems require `1 ≤ j`. -/
abbrev Iterated56Ground (j : Nat) := IterGroundAux (j - 1)

/-- Public `j`-factor family; `j = 0` deliberately has no theorem. -/
def iterated56 (j : Nat) : Family (Iterated56Ground j) :=
  iterated56Aux (j - 1)

/-- Public combined atom for `j` factors. -/
def iterated56Atom (j : Nat) : Finset (Iterated56Ground j) :=
  iterated56AtomAux (j - 1)

theorem iterated56_ground_card
    {j : Nat} (hj : 1 ≤ j) :
    Fintype.card (Iterated56Ground j) = 10 * j := by
  have h := (iterated56Aux_invariant (j - 1)).ground_card
  simpa [Nat.sub_add_cancel hj] using h

theorem iterated56_saturated
    {j : Nat} (hj : 1 ≤ j) :
    IsSaturatedKSperner (5 * j + 2) (iterated56 j) := by
  have h := (iterated56Aux_invariant (j - 1)).saturated
  simpa [iterated56, Nat.sub_add_cancel hj] using h

theorem iterated56_hasEndpoints
    {j : Nat} (hj : 1 ≤ j) :
    HasEndpoints (iterated56 j) := by
  exact (iterated56Aux_invariant (j - 1)).endpoints

theorem iterated56_homogeneousAtom
    {j : Nat} (hj : 1 ≤ j) :
    IsHomogeneousAtom (iterated56 j) (iterated56Atom j) := by
  exact (iterated56Aux_invariant (j - 1)).homogeneousAtom

theorem iterated56_small_card
    {j : Nat} (hj : 1 ≤ j) :
    (SmallPart (iterated56 j) (iterated56Atom j)).card = 28 ^ j := by
  have h := (iterated56Aux_invariant (j - 1)).small_card
  simpa [iterated56, iterated56Atom, Nat.sub_add_cancel hj] using h

theorem iterated56_large_card
    {j : Nat} (hj : 1 ≤ j) :
    (LargePart (iterated56 j) (iterated56Atom j)).card = 28 ^ j := by
  have h := (iterated56Aux_invariant (j - 1)).large_card
  simpa [iterated56, iterated56Atom, Nat.sub_add_cancel hj] using h

theorem iterated56_card
    {j : Nat} (hj : 1 ≤ j) :
    (iterated56 j).card = 2 * 28 ^ j := by
  have h := (iterated56Aux_invariant (j - 1)).total_card
  simpa [iterated56, Nat.sub_add_cancel hj] using h

/-- Ground for the iterated factor together with a symbolic standard
remainder. -/
abbrev UpperBoundGround (j s r : Nat) :=
  Iterated56Ground j ⊕ (Fin s ⊕ Fin r)

/-- The exact discrete upper-bound family before transport to `Fin n`. -/
def upperBoundFamily (j s r : Nat) : Family (UpperBoundGround j s r) :=
  composeFamilies
    (iterated56 j) (iterated56Atom j)
    (standardFamily s (Fin r)) (standardAtom s (Fin r))

/-- The combined atom in the discrete upper-bound family. -/
def upperBoundAtom (j s r : Nat) : Finset (UpperBoundGround j s r) :=
  sumSubset (iterated56Atom j) (standardAtom s (Fin r))

private theorem fin_atom_legal {r : Nat} (hr : 2 < r) :
    2 < Fintype.card (Fin r) := by
  simpa using hr

/-- The exact small part of the upper-bound family. -/
theorem upperBoundFamily_small_card
    {j s r : Nat} (hj : 1 ≤ j) (hs : s ≤ 4) (hr : 2 < r) :
    (SmallPart (upperBoundFamily j s r) (upperBoundAtom j s r)).card =
      28 ^ j * 2 ^ s := by
  have hiterAtom : (iterated56Atom j).Nonempty :=
    Finset.card_pos.mp (by
      have := (iterated56_homogeneousAtom hj).2
      omega)
  have hstandardAtom : (standardAtom s (Fin r)).Nonempty :=
    Finset.card_pos.mp (by
      have := (standard_homogeneousAtom (s := s) (H := Fin r)
        (fin_atom_legal hr)).2
      omega)
  have hcard := compose_small_card
    (F₁ := iterated56 j) (H₁ := iterated56Atom j)
    (F₂ := standardFamily s (Fin r)) (H₂ := standardAtom s (Fin r))
    hiterAtom hstandardAtom
  rw [iterated56_small_card hj,
    standard_small_card (s := s) (H := Fin r) (fin_atom_legal hr)] at hcard
  simpa [upperBoundFamily, upperBoundAtom] using hcard

/-- The exact large part of the upper-bound family. -/
theorem upperBoundFamily_large_card
    {j s r : Nat} (hj : 1 ≤ j) (hs : s ≤ 4) (hr : 2 < r) :
    (LargePart (upperBoundFamily j s r) (upperBoundAtom j s r)).card =
      28 ^ j * 2 ^ s := by
  have hiterAtom : (iterated56Atom j).Nonempty :=
    Finset.card_pos.mp (by
      have := (iterated56_homogeneousAtom hj).2
      omega)
  have hstandardAtom : (standardAtom s (Fin r)).Nonempty :=
    Finset.card_pos.mp (by
      have := (standard_homogeneousAtom (s := s) (H := Fin r)
        (fin_atom_legal hr)).2
      omega)
  have hcard := compose_large_card
    (F₁ := iterated56 j) (H₁ := iterated56Atom j)
    (F₂ := standardFamily s (Fin r)) (H₂ := standardAtom s (Fin r))
    hiterAtom hstandardAtom
  rw [iterated56_large_card hj,
    standard_large_card (s := s) (H := Fin r) (fin_atom_legal hr)] at hcard
  simpa [upperBoundFamily, upperBoundAtom] using hcard

/-- Exact saturation parameter after adjoining the standard remainder. -/
theorem upperBoundFamily_saturated
    {j s r : Nat} (hj : 1 ≤ j) (hs : s ≤ 4) (hr : 2 < r) :
    IsSaturatedKSperner (5 * j + 2 + s) (upperBoundFamily j s r) := by
  have hcompose := compose_saturated
    (iterated56_saturated hj)
    (standard_saturated (s := s) (H := Fin r) (fin_atom_legal hr))
    (iterated56_hasEndpoints hj)
    (standard_hasEndpoints (s := s) (H := Fin r) (fin_atom_legal hr))
    (iterated56_homogeneousAtom hj)
    (standard_homogeneousAtom (s := s) (H := Fin r) (fin_atom_legal hr))
  change IsSaturatedKSperner (5 * j + 2 + s)
    (composeFamilies
      (iterated56 j) (iterated56Atom j)
      (standardFamily s (Fin r)) (standardAtom s (Fin r)))
  convert hcompose using 1 <;> omega

/-- Endpoint preservation for the exact discrete upper-bound family. -/
theorem upperBoundFamily_hasEndpoints
    {j s r : Nat} (hj : 1 ≤ j) (hs : s ≤ 4) (hr : 2 < r) :
    HasEndpoints (upperBoundFamily j s r) := by
  exact compose_hasEndpoints
    (iterated56_hasEndpoints hj)
    (standard_hasEndpoints (s := s) (H := Fin r) (fin_atom_legal hr))

/-- Source-facing endpoint alias. -/
theorem upperBoundFamily_endpoints
    {j s r : Nat} (hj : 1 ≤ j) (hs : s ≤ 4) (hr : 2 < r) :
    HasEndpoints (upperBoundFamily j s r) :=
  upperBoundFamily_hasEndpoints hj hs hr

/-- The combined atom remains homogeneous. -/
theorem upperBoundFamily_homogeneousAtom
    {j s r : Nat} (hj : 1 ≤ j) (hs : s ≤ 4) (hr : 2 < r) :
    IsHomogeneousAtom (upperBoundFamily j s r) (upperBoundAtom j s r) := by
  exact compose_homogeneousAtom
    (iterated56_hasEndpoints hj)
    (standard_hasEndpoints (s := s) (H := Fin r) (fin_atom_legal hr))
    (iterated56_homogeneousAtom hj)
    (standard_homogeneousAtom (s := s) (H := Fin r) (fin_atom_legal hr))

/-- Exact product-sum cardinality, normalized to the Martin--Veldt formula. -/
theorem upperBoundFamily_card
    {j s r : Nat} (hj : 1 ≤ j) (hs : s ≤ 4) (hr : 2 < r) :
    (upperBoundFamily j s r).card = 2 ^ (s + 1) * 28 ^ j := by
  have hiterAtom : (iterated56Atom j).Nonempty :=
    Finset.card_pos.mp (by
      have := (iterated56_homogeneousAtom hj).2
      omega)
  have hcard := compose_card
    (F₁ := iterated56 j) (H₁ := iterated56Atom j)
    (F₂ := standardFamily s (Fin r)) (H₂ := standardAtom s (Fin r))
    hiterAtom
  rw [iterated56_small_card hj, iterated56_large_card hj,
    standard_small_card (s := s) (H := Fin r) (fin_atom_legal hr),
    standard_large_card (s := s) (H := Fin r) (fin_atom_legal hr)] at hcard
  rw [upperBoundFamily]
  calc
    _ = 28 ^ j * 2 ^ s + 28 ^ j * 2 ^ s := hcard
    _ = 2 ^ (s + 1) * 28 ^ j := by rw [pow_succ]; ring

/-- Full exact discrete-family bundle. -/
theorem upperBoundFamily_full
    {j s r : Nat} (hj : 1 ≤ j) (hs : s ≤ 4) (hr : 2 < r) :
    IsSaturatedKSperner (5 * j + 2 + s) (upperBoundFamily j s r) ∧
      HasEndpoints (upperBoundFamily j s r) ∧
      IsHomogeneousAtom (upperBoundFamily j s r) (upperBoundAtom j s r) ∧
      (SmallPart (upperBoundFamily j s r) (upperBoundAtom j s r)).card =
        28 ^ j * 2 ^ s ∧
      (LargePart (upperBoundFamily j s r) (upperBoundAtom j s r)).card =
        28 ^ j * 2 ^ s ∧
      (upperBoundFamily j s r).card = 2 ^ (s + 1) * 28 ^ j := by
  exact ⟨upperBoundFamily_saturated hj hs hr,
    upperBoundFamily_hasEndpoints hj hs hr,
    upperBoundFamily_homogeneousAtom hj hs hr,
    upperBoundFamily_small_card hj hs hr,
    upperBoundFamily_large_card hj hs hr,
    upperBoundFamily_card hj hs hr⟩

/-- Explicit threshold for the every-sufficiently-large-ground theorem. -/
def upperBoundThreshold (j s : Nat) : Nat :=
  10 * j + s + 3

/-- Size of the standard atom at target ground cardinality `n`. -/
def upperBoundRemainder (j s n : Nat) : Nat :=
  n - (10 * j + s)

/-- At and above the threshold, the standard atom has at least three points. -/
theorem upperBoundRemainder_legal
    {j s n : Nat} (hn : upperBoundThreshold j s ≤ n) :
    2 < upperBoundRemainder j s n := by
  unfold upperBoundThreshold upperBoundRemainder at *
  omega

/-- The pre-transport ground has exactly the requested cardinality. -/
theorem upperBoundGround_card_at
    {j s n : Nat} (hj : 1 ≤ j)
    (hn : upperBoundThreshold j s ≤ n) :
    Fintype.card
      (UpperBoundGround j s (upperBoundRemainder j s n)) = n := by
  simp only [UpperBoundGround, Fintype.card_sum, Fintype.card_fin]
  rw [iterated56_ground_card hj]
  unfold upperBoundThreshold upperBoundRemainder at *
  omega

/-- A cardinality-certified equivalence to the requested `Fin n` ground. -/
noncomputable def upperBoundGroundEquivFin
    {j s n : Nat} (hj : 1 ≤ j)
    (hn : upperBoundThreshold j s ≤ n) :
    UpperBoundGround j s (upperBoundRemainder j s n) ≃ Fin n :=
  Fintype.equivFinOfCardEq (upperBoundGround_card_at hj hn)

/-- Cardinality is invariant under ground equivalence. -/
@[simp] theorem mapFamily_card
    {α β : Type u} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (F : Family α) :
    (mapFamily e F).card = F.card := by
  change (Finset.map e.finsetCongr.toEmbedding F).card = F.card
  exact Finset.card_map _

/-- The exact upper-bound family transported to `Fin n`. -/
noncomputable def upperBoundFamilyFin
    {j s n : Nat} (hj : 1 ≤ j)
    (hn : upperBoundThreshold j s ≤ n) : Family (Fin n) :=
  mapFamily (upperBoundGroundEquivFin hj hn)
    (upperBoundFamily j s (upperBoundRemainder j s n))

/-- Explicit-threshold construction on every target `Fin n`. -/
theorem exists_upperBoundFamily_fin_at
    (j : Nat) (hj : 1 ≤ j)
    (s : Nat) (hs : s ≤ 4)
    (n : Nat) (hn : upperBoundThreshold j s ≤ n) :
    ∃ F : Family (Fin n),
      IsSaturatedKSperner (5 * j + 2 + s) F ∧
      F.card = 2 ^ (s + 1) * 28 ^ j := by
  refine ⟨upperBoundFamilyFin hj hn, ?_, ?_⟩
  · apply (isSaturatedKSperner_mapFamily_iff
      (upperBoundGroundEquivFin hj hn)
      (5 * j + 2 + s)
      (upperBoundFamily j s (upperBoundRemainder j s n))).mpr
    exact upperBoundFamily_saturated hj hs
      (upperBoundRemainder_legal hn)
  · simp [upperBoundFamilyFin,
      upperBoundFamily_card hj hs (upperBoundRemainder_legal hn)]

/-- For every sufficiently large ground size—not merely a subsequence—the
exact Martin--Veldt finite-family formula is attained. -/
theorem exists_upperBoundFamily_fin
    (j : Nat) (hj : 1 ≤ j)
    (s : Nat) (hs : s ≤ 4) :
    ∃ N, ∀ n, N ≤ n →
      ∃ F : Family (Fin n),
        IsSaturatedKSperner (5 * j + 2 + s) F ∧
        F.card = 2 ^ (s + 1) * 28 ^ j := by
  exact ⟨upperBoundThreshold j s,
    fun n hn => exists_upperBoundFamily_fin_at j hj s hs n hn⟩

end AiMathLab.P0053UpperBound
