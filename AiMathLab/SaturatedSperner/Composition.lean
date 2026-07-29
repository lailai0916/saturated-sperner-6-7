import AiMathLab.SaturatedSperner.HomogeneousLayers

/-!
# Composition of saturated Sperner systems

This module gives the tagged-sum form of Morrison--Noel--Scott Lemma 18.
The two endpoint hypotheses remain explicit in the source-facing saturation
theorems.  The proof is symbolic in both ground types: it uses projected
change counts for chain-freeness and true-through partial-atom chains for
saturation.
-/

universe u v

namespace AiMathLab.SaturatedSperner

variable {α : Type u} {β : Type v}
  [DecidableEq α] [DecidableEq β]

/-- Both Boolean-lattice endpoints belong to a finite family. -/
def HasEndpoints [Fintype α] (F : Family α) : Prop :=
  (∅ : Finset α) ∈ F ∧ Finset.univ ∈ F

/-- Tagged disjoint union of two finite subsets. -/
def sumSubset (A : Finset α) (B : Finset β) : Finset (α ⊕ β) :=
  A.disjSum B

/-- Projection to the left tagged ground. -/
def leftProjection (S : Finset (α ⊕ β)) : Finset α :=
  S.toLeft

/-- Projection to the right tagged ground. -/
def rightProjection (S : Finset (α ⊕ β)) : Finset β :=
  S.toRight

@[simp] theorem inl_mem_sumSubset
    {A : Finset α} {B : Finset β} {a : α} :
    Sum.inl a ∈ sumSubset A B ↔ a ∈ A := by
  simp [sumSubset]

@[simp] theorem inr_mem_sumSubset
    {A : Finset α} {B : Finset β} {b : β} :
    Sum.inr b ∈ sumSubset A B ↔ b ∈ B := by
  simp [sumSubset]

@[simp] theorem leftProjection_sumSubset
    (A : Finset α) (B : Finset β) :
    leftProjection (sumSubset A B) = A := by
  simp [leftProjection, sumSubset]

@[simp] theorem rightProjection_sumSubset
    (A : Finset α) (B : Finset β) :
    rightProjection (sumSubset A B) = B := by
  simp [rightProjection, sumSubset]

@[simp] theorem sumSubset_projections (S : Finset (α ⊕ β)) :
    sumSubset (leftProjection S) (rightProjection S) = S := by
  ext x
  cases x <;> simp [sumSubset, leftProjection, rightProjection]

@[simp] theorem leftProjection_empty :
    leftProjection (∅ : Finset (α ⊕ β)) = ∅ := by
  ext a
  simp [leftProjection]

@[simp] theorem rightProjection_empty :
    rightProjection (∅ : Finset (α ⊕ β)) = ∅ := by
  ext b
  simp [rightProjection]

@[simp] theorem leftProjection_univ [Fintype α] [Fintype β] :
    leftProjection (Finset.univ : Finset (α ⊕ β)) = Finset.univ := by
  ext a
  simp [leftProjection]

@[simp] theorem rightProjection_univ [Fintype α] [Fintype β] :
    rightProjection (Finset.univ : Finset (α ⊕ β)) = Finset.univ := by
  ext b
  simp [rightProjection]

theorem sumSubset_injective :
    Function.Injective
      (fun p : Finset α × Finset β => sumSubset p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · simpa using congrArg leftProjection hpq
  · simpa using congrArg rightProjection hpq

theorem projections_injective :
    Function.Injective
      (fun S : Finset (α ⊕ β) =>
        (leftProjection S, rightProjection S)) := by
  intro S T h
  have hleft : leftProjection S = leftProjection T :=
    congrArg Prod.fst h
  have hright : rightProjection S = rightProjection T :=
    congrArg Prod.snd h
  rw [← sumSubset_projections S, ← sumSubset_projections T,
    hleft, hright]

theorem sumSubset_subset_iff
    {A C : Finset α} {B D : Finset β} :
    sumSubset A B ⊆ sumSubset C D ↔ A ⊆ C ∧ B ⊆ D := by
  rw [sumSubset, Finset.disjSum_subset]
  simp [sumSubset, leftProjection, rightProjection]

theorem sumSubset_subset_arbitrary_iff
    {A : Finset α} {B : Finset β} {S : Finset (α ⊕ β)} :
    sumSubset A B ⊆ S ↔
      A ⊆ leftProjection S ∧ B ⊆ rightProjection S := by
  simpa [sumSubset, leftProjection, rightProjection] using
    (Finset.disjSum_subset (s := A) (t := B) (u := S))

theorem arbitrary_subset_sumSubset_iff
    {S : Finset (α ⊕ β)} {A : Finset α} {B : Finset β} :
    S ⊆ sumSubset A B ↔
      leftProjection S ⊆ A ∧ rightProjection S ⊆ B := by
  constructor
  · intro h
    constructor
    · intro a ha
      have : Sum.inl a ∈ S := by
        simpa [leftProjection] using ha
      exact inl_mem_sumSubset.mp (h this)
    · intro b hb
      have : Sum.inr b ∈ S := by
        simpa [rightProjection] using hb
      exact inr_mem_sumSubset.mp (h this)
  · rintro ⟨hleft, hright⟩ x hx
    cases x with
    | inl a =>
        exact inl_mem_sumSubset.mpr
          (hleft (by simpa [leftProjection] using hx))
    | inr b =>
        exact inr_mem_sumSubset.mpr
          (hright (by simpa [rightProjection] using hx))

theorem sumSubset_ssubset_control
    {A C : Finset α} {B D : Finset β} :
    sumSubset A B ⊂ sumSubset C D ↔
      (A ⊂ C ∧ B ⊆ D) ∨ (A ⊆ C ∧ B ⊂ D) := by
  constructor
  · intro h
    have hsub := sumSubset_subset_iff.mp h.le
    by_cases hAC : A = C
    · right
      refine ⟨by simpa [hAC], ?_⟩
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub.2, ?_⟩
      intro hBD
      exact h.ne (by simp [hAC, hBD])
    · left
      exact ⟨Finset.ssubset_iff_subset_ne.mpr ⟨hsub.1, hAC⟩,
        hsub.2⟩
  · rintro (⟨hAC, hBD⟩ | ⟨hAC, hBD⟩)
    · apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨sumSubset_subset_iff.mpr ⟨hAC.le, hBD⟩, ?_⟩
      intro hEq
      exact hAC.ne (by simpa using congrArg leftProjection hEq)
    · apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨sumSubset_subset_iff.mpr ⟨hAC, hBD.le⟩, ?_⟩
      intro hEq
      exact hBD.ne (by simpa using congrArg rightProjection hEq)

theorem projections_ssubset_control
    {S T : Finset (α ⊕ β)} (h : S ⊂ T) :
    (leftProjection S ⊂ leftProjection T ∧
        rightProjection S ⊆ rightProjection T) ∨
      (leftProjection S ⊆ leftProjection T ∧
        rightProjection S ⊂ rightProjection T) := by
  rw [← sumSubset_projections S, ← sumSubset_projections T] at h
  exact sumSubset_ssubset_control.mp h

theorem leftProjection_mono
    {S T : Finset (α ⊕ β)} (h : S ⊆ T) :
    leftProjection S ⊆ leftProjection T := by
  intro a ha
  have haS : Sum.inl a ∈ S := by
    simpa [leftProjection] using ha
  have haT := h haS
  simpa [leftProjection] using haT

theorem rightProjection_mono
    {S T : Finset (α ⊕ β)} (h : S ⊆ T) :
    rightProjection S ⊆ rightProjection T := by
  intro b hb
  have hbS : Sum.inr b ∈ S := by
    simpa [rightProjection] using hb
  have hbT := h hbS
  simpa [rightProjection] using hbT

@[simp] theorem sumSubset_card (A : Finset α) (B : Finset β) :
    (sumSubset A B).card = A.card + B.card := by
  exact Finset.card_disjSum A B

@[simp] theorem sumSubset_empty :
    sumSubset (∅ : Finset α) (∅ : Finset β) = ∅ := by
  ext x
  cases x <;> simp

@[simp] theorem sumSubset_univ [Fintype α] [Fintype β] :
    sumSubset (Finset.univ : Finset α) (Finset.univ : Finset β) =
      (Finset.univ : Finset (α ⊕ β)) := by
  ext x
  cases x <;> simp

/-- The injective tagged image of a Cartesian product of families. -/
def productFamily (F : Family α) (G : Family β) : Family (α ⊕ β) :=
  (F ×ˢ G).map
    ⟨fun p => sumSubset p.1 p.2, sumSubset_injective⟩

@[simp] theorem mem_productFamily
    {F : Family α} {G : Family β} {S : Finset (α ⊕ β)} :
    S ∈ productFamily F G ↔
      leftProjection S ∈ F ∧ rightProjection S ∈ G := by
  constructor
  · intro hS
    rw [productFamily, Finset.mem_map] at hS
    rcases hS with ⟨p, hp, hpS⟩
    subst S
    simpa using hp
  · rintro ⟨hleft, hright⟩
    rw [productFamily, Finset.mem_map]
    refine ⟨(leftProjection S, rightProjection S), ?_, ?_⟩
    · simpa using And.intro hleft hright
    · exact sumSubset_projections S

@[simp] theorem productFamily_card (F : Family α) (G : Family β) :
    (productFamily F G).card = F.card * G.card := by
  simp [productFamily]

/-- MNS composition: small--small pairs together with large--large pairs. -/
def composeFamilies
    (F₁ : Family α) (H₁ : Finset α)
    (F₂ : Family β) (H₂ : Finset β) :
    Family (α ⊕ β) :=
  productFamily (SmallPart F₁ H₁) (SmallPart F₂ H₂) ∪
    productFamily (LargePart F₁ H₁) (LargePart F₂ H₂)

@[simp] theorem mem_composeFamilies
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    {S : Finset (α ⊕ β)} :
    S ∈ composeFamilies F₁ H₁ F₂ H₂ ↔
      (leftProjection S ∈ SmallPart F₁ H₁ ∧
        rightProjection S ∈ SmallPart F₂ H₂) ∨
      (leftProjection S ∈ LargePart F₁ H₁ ∧
        rightProjection S ∈ LargePart F₂ H₂) := by
  simp [composeFamilies]

private theorem sumAtom_nonempty_left
    {H₁ : Finset α} {H₂ : Finset β} (hH₁ : H₁.Nonempty) :
    (sumSubset H₁ H₂).Nonempty := by
  rcases hH₁ with ⟨a, ha⟩
  exact ⟨Sum.inl a, inl_mem_sumSubset.mpr ha⟩

theorem compose_smallPart
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hH₁ : H₁.Nonempty) (hH₂ : H₂.Nonempty) :
    SmallPart (composeFamilies F₁ H₁ F₂ H₂) (sumSubset H₁ H₂) =
      productFamily (SmallPart F₁ H₁) (SmallPart F₂ H₂) := by
  ext S
  constructor
  · intro hS
    rcases mem_smallPart.mp hS with ⟨hSG, hdisj⟩
    rcases mem_composeFamilies.mp hSG with hsmall | hlarge
    · exact mem_productFamily.mpr hsmall
    · rcases hH₁ with ⟨a, ha⟩
      have haS : Sum.inl a ∈ S := by
        have : a ∈ leftProjection S :=
          (mem_largePart.mp hlarge.1).2 ha
        simpa [leftProjection] using this
      exact False.elim
        ((Finset.disjoint_left.mp hdisj) haS
          (inl_mem_sumSubset.mpr ha))
  · intro hS
    have hp := mem_productFamily.mp hS
    apply mem_smallPart.mpr
    refine ⟨mem_composeFamilies.mpr (Or.inl hp), ?_⟩
    rw [Finset.disjoint_left]
    intro x hxS hxH
    cases x with
    | inl a =>
        exact (Finset.disjoint_left.mp (mem_smallPart.mp hp.1).2)
          (by simpa [leftProjection] using hxS)
          (inl_mem_sumSubset.mp hxH)
    | inr b =>
        exact (Finset.disjoint_left.mp (mem_smallPart.mp hp.2).2)
          (by simpa [rightProjection] using hxS)
          (inr_mem_sumSubset.mp hxH)

theorem compose_largePart
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hH₁ : H₁.Nonempty) (hH₂ : H₂.Nonempty) :
    LargePart (composeFamilies F₁ H₁ F₂ H₂) (sumSubset H₁ H₂) =
      productFamily (LargePart F₁ H₁) (LargePart F₂ H₂) := by
  ext S
  constructor
  · intro hS
    rcases mem_largePart.mp hS with ⟨hSG, hsub⟩
    rcases mem_composeFamilies.mp hSG with hsmall | hlarge
    · rcases hH₁ with ⟨a, ha⟩
      have haS : Sum.inl a ∈ S := hsub (inl_mem_sumSubset.mpr ha)
      exact False.elim
        ((Finset.disjoint_left.mp (mem_smallPart.mp hsmall.1).2)
          (by simpa [leftProjection] using haS) ha)
    · exact mem_productFamily.mpr hlarge
  · intro hS
    have hp := mem_productFamily.mp hS
    apply mem_largePart.mpr
    refine ⟨mem_composeFamilies.mpr (Or.inr hp), ?_⟩
    intro x hx
    cases x with
    | inl a =>
        have : a ∈ leftProjection S :=
          (mem_largePart.mp hp.1).2 (inl_mem_sumSubset.mp hx)
        simpa [leftProjection] using this
    | inr b =>
        have : b ∈ rightProjection S :=
          (mem_largePart.mp hp.2).2 (inr_mem_sumSubset.mp hx)
        simpa [rightProjection] using this

theorem compose_small_card
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hH₁ : H₁.Nonempty) (hH₂ : H₂.Nonempty) :
    (SmallPart (composeFamilies F₁ H₁ F₂ H₂)
      (sumSubset H₁ H₂)).card =
      (SmallPart F₁ H₁).card * (SmallPart F₂ H₂).card := by
  rw [compose_smallPart hH₁ hH₂, productFamily_card]

theorem compose_large_card
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hH₁ : H₁.Nonempty) (hH₂ : H₂.Nonempty) :
    (LargePart (composeFamilies F₁ H₁ F₂ H₂)
      (sumSubset H₁ H₂)).card =
      (LargePart F₁ H₁).card * (LargePart F₂ H₂).card := by
  rw [compose_largePart hH₁ hH₂, productFamily_card]

theorem compose_card
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hH₁ : H₁.Nonempty) :
    (composeFamilies F₁ H₁ F₂ H₂).card =
      (SmallPart F₁ H₁).card * (SmallPart F₂ H₂).card +
      (LargePart F₁ H₁).card * (LargePart F₂ H₂).card := by
  rw [composeFamilies, Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_left]
    intro S hsmall hlarge
    have hs := mem_productFamily.mp hsmall
    have hl := mem_productFamily.mp hlarge
    exact Finset.disjoint_left.mp (smallPart_largePart_disjoint hH₁)
      hs.1 hl.1

theorem compose_hasEndpoints
    [Fintype α] [Fintype β]
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hend₁ : HasEndpoints F₁) (hend₂ : HasEndpoints F₂) :
    HasEndpoints (composeFamilies F₁ H₁ F₂ H₂) := by
  constructor
  · apply mem_composeFamilies.mpr
    left
    constructor <;> apply mem_smallPart.mpr
    · exact ⟨hend₁.1, by simp⟩
    · exact ⟨hend₂.1, by simp⟩
  · apply mem_composeFamilies.mpr
    right
    constructor
    · apply mem_largePart.mpr
      exact ⟨by simpa using hend₁.2, by simp⟩
    · apply mem_largePart.mpr
      exact ⟨by simpa using hend₂.2, by simp⟩

/-- The all-or-none part of the combined tagged atom. -/
theorem compose_atomBlock
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hblock₁ : IsAtomBlock F₁ H₁)
    (hblock₂ : IsAtomBlock F₂ H₂) :
    IsAtomBlock (composeFamilies F₁ H₁ F₂ H₂) (sumSubset H₁ H₂) := by
  intro S hS
  rcases mem_composeFamilies.mp hS with hsmall | hlarge
  · left
    rw [Finset.disjoint_left]
    intro x hxS hxH
    cases x with
    | inl a =>
        exact (Finset.disjoint_left.mp (mem_smallPart.mp hsmall.1).2)
          (by simpa [leftProjection] using hxS)
          (inl_mem_sumSubset.mp hxH)
    | inr b =>
        exact (Finset.disjoint_left.mp (mem_smallPart.mp hsmall.2).2)
          (by simpa [rightProjection] using hxS)
          (inr_mem_sumSubset.mp hxH)
  · right
    intro x hxH
    cases x with
    | inl a =>
        have ha := (mem_largePart.mp hlarge.1).2
          (inl_mem_sumSubset.mp hxH)
        simpa [leftProjection] using ha
    | inr b =>
        have hb := (mem_largePart.mp hlarge.2).2
          (inr_mem_sumSubset.mp hxH)
        simpa [rightProjection] using hb

private theorem factor_block_counterexample
    {γ : Type*} [DecidableEq γ]
    {F : Family γ} {H K : Finset γ}
    (hblock : IsAtomBlock F H)
    (hK : ¬ IsAtomBlock F K) :
    ∃ A : Finset γ, A ∈ F ∧
      ¬ Disjoint A K ∧ ¬ K ⊆ A ∧
      (A ∈ SmallPart F H ∨ A ∈ LargePart F H) := by
  classical
  simp only [IsAtomBlock] at hK
  push_neg at hK
  rcases hK with ⟨A, hAF, hAdisj, hKsub⟩
  refine ⟨A, hAF, hAdisj, hKsub, ?_⟩
  rcases hblock A hAF with hsmall | hlarge
  · exact Or.inl (mem_smallPart.mpr ⟨hAF, hsmall⟩)
  · exact Or.inr (mem_largePart.mpr ⟨hAF, hlarge⟩)

private theorem tagged_witness_breaks_block_left
    [Fintype β]
    {F₁ : Family α} {H₁ K₁ A : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hend₂ : HasEndpoints F₂)
    (hA : A ∈ SmallPart F₁ H₁ ∨ A ∈ LargePart F₁ H₁)
    (hinter : ¬ Disjoint A K₁) (hnsub : ¬ K₁ ⊆ A)
    {K : Finset (α ⊕ β)} (hproj : leftProjection K = K₁) :
    ¬ IsAtomBlock (composeFamilies F₁ H₁ F₂ H₂) K := by
  intro hblock
  rcases hA with hsmall | hlarge
  · let U := sumSubset A (∅ : Finset β)
    have hUF : U ∈ composeFamilies F₁ H₁ F₂ H₂ := by
      apply mem_composeFamilies.mpr
      left
      refine ⟨by simpa [U] using hsmall, ?_⟩
      apply mem_smallPart.mpr
      exact ⟨by simpa [U] using hend₂.1,
        by rw [show rightProjection U = ∅ by simp [U]]; simp⟩
    rcases hblock U hUF with hdisj | hsub
    · apply hinter
      rw [Finset.disjoint_left]
      intro a haA haK
      rw [← hproj] at haK
      exact (Finset.disjoint_left.mp hdisj)
        (inl_mem_sumSubset.mpr haA)
        (by simpa [leftProjection] using haK)
    · apply hnsub
      intro a haK
      rw [← hproj] at haK
      have haTagged : Sum.inl a ∈ K := by
        simpa [leftProjection] using haK
      exact inl_mem_sumSubset.mp (hsub haTagged)
  · let U := sumSubset A (Finset.univ : Finset β)
    have hUF : U ∈ composeFamilies F₁ H₁ F₂ H₂ := by
      apply mem_composeFamilies.mpr
      right
      refine ⟨by simpa [U] using hlarge, ?_⟩
      apply mem_largePart.mpr
      exact ⟨by simpa [U] using hend₂.2,
        by simp [U, rightProjection, sumSubset]⟩
    rcases hblock U hUF with hdisj | hsub
    · apply hinter
      rw [Finset.disjoint_left]
      intro a haA haK
      rw [← hproj] at haK
      exact (Finset.disjoint_left.mp hdisj)
        (inl_mem_sumSubset.mpr haA)
        (by simpa [leftProjection] using haK)
    · apply hnsub
      intro a haK
      rw [← hproj] at haK
      have haTagged : Sum.inl a ∈ K := by
        simpa [leftProjection] using haK
      exact inl_mem_sumSubset.mp (hsub haTagged)

private theorem tagged_witness_breaks_block_right
    [Fintype α]
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ K₂ B : Finset β}
    (hend₁ : HasEndpoints F₁)
    (hB : B ∈ SmallPart F₂ H₂ ∨ B ∈ LargePart F₂ H₂)
    (hinter : ¬ Disjoint B K₂) (hnsub : ¬ K₂ ⊆ B)
    {K : Finset (α ⊕ β)} (hproj : rightProjection K = K₂) :
    ¬ IsAtomBlock (composeFamilies F₁ H₁ F₂ H₂) K := by
  intro hblock
  rcases hB with hsmall | hlarge
  · let U := sumSubset (∅ : Finset α) B
    have hUF : U ∈ composeFamilies F₁ H₁ F₂ H₂ := by
      apply mem_composeFamilies.mpr
      left
      refine ⟨?_, by simpa [U] using hsmall⟩
      apply mem_smallPart.mpr
      exact ⟨by simpa [U] using hend₁.1,
        by rw [show leftProjection U = ∅ by simp [U]]; simp⟩
    rcases hblock U hUF with hdisj | hsub
    · apply hinter
      rw [Finset.disjoint_left]
      intro b hbB hbK
      rw [← hproj] at hbK
      exact (Finset.disjoint_left.mp hdisj)
        (inr_mem_sumSubset.mpr hbB)
        (by simpa [rightProjection] using hbK)
    · apply hnsub
      intro b hbK
      rw [← hproj] at hbK
      have hbTagged : Sum.inr b ∈ K := by
        simpa [rightProjection] using hbK
      exact inr_mem_sumSubset.mp (hsub hbTagged)
  · let U := sumSubset (Finset.univ : Finset α) B
    have hUF : U ∈ composeFamilies F₁ H₁ F₂ H₂ := by
      apply mem_composeFamilies.mpr
      right
      refine ⟨?_, by simpa [U] using hlarge⟩
      apply mem_largePart.mpr
      exact ⟨by simpa [U] using hend₁.2,
        by simp [U, leftProjection, sumSubset]⟩
    rcases hblock U hUF with hdisj | hsub
    · apply hinter
      rw [Finset.disjoint_left]
      intro b hbB hbK
      rw [← hproj] at hbK
      exact (Finset.disjoint_left.mp hdisj)
        (inr_mem_sumSubset.mpr hbB)
        (by simpa [rightProjection] using hbK)
    · apply hnsub
      intro b hbK
      rw [← hproj] at hbK
      have hbTagged : Sum.inr b ∈ K := by
        simpa [rightProjection] using hbK
      exact inr_mem_sumSubset.mp (hsub hbTagged)

theorem compose_atom_maximal
    [Fintype α] [Fintype β]
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hend₁ : HasEndpoints F₁) (hend₂ : HasEndpoints F₂)
    (hAtom₁ : IsAtom F₁ H₁) (hAtom₂ : IsAtom F₂ H₂) :
    ∀ K, sumSubset H₁ H₂ ⊂ K →
      ¬ IsAtomBlock (composeFamilies F₁ H₁ F₂ H₂) K := by
  intro K hHK
  have htagged :
      sumSubset H₁ H₂ ⊂
        sumSubset (leftProjection K) (rightProjection K) := by
    simpa using hHK
  rcases sumSubset_ssubset_control.mp htagged with hleft | hright
  · have hnot := hAtom₁.2 (leftProjection K) hleft.1
    rcases factor_block_counterexample hAtom₁.1 hnot with
      ⟨A, hAF, hinter, hnsub, hpart⟩
    exact tagged_witness_breaks_block_left hend₂ hpart hinter hnsub rfl
  · have hnot := hAtom₂.2 (rightProjection K) hright.2
    rcases factor_block_counterexample hAtom₂.1 hnot with
      ⟨B, hBF, hinter, hnsub, hpart⟩
    exact tagged_witness_breaks_block_right hend₁ hpart hinter hnsub rfl

theorem compose_homogeneousAtom
    [Fintype α] [Fintype β]
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hend₁ : HasEndpoints F₁) (hend₂ : HasEndpoints F₂)
    (hH₁ : IsHomogeneousAtom F₁ H₁)
    (hH₂ : IsHomogeneousAtom F₂ H₂) :
    IsHomogeneousAtom (composeFamilies F₁ H₁ F₂ H₂)
      (sumSubset H₁ H₂) := by
  refine ⟨⟨compose_atomBlock hH₁.1.1 hH₂.1.1,
      compose_atom_maximal hend₁ hend₂ hH₁.1 hH₂.1⟩, ?_⟩
  rw [sumSubset_card]
  have hcard := hH₁.2
  omega

/-- The source hypotheses force both Sperner parameters past the truncated
subtraction boundary. -/
theorem two_le_of_saturated_endpoints_homogeneous
    [Fintype α]
    {k : Nat} {F : Family α} {H : Finset α}
    (hsat : IsSaturatedKSperner k F)
    (hend : HasEndpoints F)
    (hH : IsHomogeneousAtom F H) :
    2 ≤ k := by
  have hcard := hH.2
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty α := ⟨Classical.choose hHne⟩
  have hempty_univ : (∅ : Finset α) ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    exact ⟨by simp, (Finset.nonempty_iff_ne_empty.mp Finset.univ_nonempty).symm⟩
  have htwo : HasStrictChainLength 2 F :=
    ⟨Finset.univ, hend.2, ∅, hend.1, hempty_univ⟩
  by_contra hk
  have hle : k + 1 ≤ 2 := by omega
  exact hsat.1 (hasStrictChainLength_of_le hle htwo)

/-! ## Projected change counts -/

/-- Number of adjacent strict changes in a possibly stuttering trace. -/
def strictChangeCount {γ : Type*} [DecidableEq γ] : List γ → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: tail =>
      (if x = y then 0 else 1) + strictChangeCount (y :: tail)

/-- Number of adjacent steps at which both coordinates change. -/
private def simultaneousChangeCount
    {γ δ : Type*} [DecidableEq γ] [DecidableEq δ] :
    List (γ × δ) → Nat
  | [] => 0
  | [_] => 0
  | p :: q :: tail =>
      (if p.1 ≠ q.1 ∧ p.2 ≠ q.2 then 1 else 0) +
        simultaneousChangeCount (q :: tail)

private theorem pair_change_count_identity
    {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (p : List (γ × δ)) :
    strictChangeCount (p.map Prod.fst) +
        strictChangeCount (p.map Prod.snd) =
      strictChangeCount p + simultaneousChangeCount p := by
  induction p using List.twoStepInduction with
  | nil => rfl
  | singleton p => rfl
  | cons_cons p q tail ih ih₂ =>
      have ht :
          strictChangeCount (q.1 :: tail.map Prod.fst) +
              strictChangeCount (q.2 :: tail.map Prod.snd) =
            strictChangeCount (q :: tail) +
              simultaneousChangeCount (q :: tail) := by
        simpa only [List.map_cons] using ih₂ q
      simp only [List.map_cons, strictChangeCount,
        simultaneousChangeCount]
      by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2
      all_goals simp [h₁, h₂, Prod.ext_iff]
      all_goals omega

private theorem strictChangeCount_eq_length_sub_one_of_chain
    {γ : Type*} [DecidableEq γ]
    (l : List γ) (h : l.IsChain (· ≠ ·)) :
    strictChangeCount l = l.length - 1 := by
  induction l using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y tail ih ih₂ =>
      have hp := List.isChain_cons_cons.mp h
      have ht := ih₂ y hp.2
      simp [strictChangeCount, hp.1, ht]
      omega

/-- Adjacent change count is the length of the stutter-compressed trace minus
one. -/
theorem strictChangeCount_eq_compress_length_sub_one
    {γ : Type*} [DecidableEq γ] (l : List γ) :
    strictChangeCount l =
      (l.destutter (· ≠ ·)).length - 1 := by
  induction l using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y tail ih ih₂ =>
      have ht := ih₂ y
      by_cases hxy : x = y
      · subst y
        rw [List.destutter_cons_cons, if_neg (not_ne_iff.mpr rfl)]
        rw [← List.destutter_cons']
        simpa [strictChangeCount] using ht
      · rw [List.destutter_cons_cons, if_pos hxy]
        rw [← List.destutter_cons']
        simp only [List.length_cons, strictChangeCount, if_neg hxy]
        rw [ht]
        have hnonempty :
            ((y :: tail).destutter (· ≠ ·)) ≠ [] := by simp
        have hpos :
            0 < ((y :: tail).destutter (· ≠ ·)).length :=
          List.length_pos_iff.mpr hnonempty
        omega

private theorem isChain_ssubset_of_subset_of_ne
    {γ : Type*} [DecidableEq γ]
    (l : List (Finset γ))
    (hsub : l.IsChain (· ⊆ ·))
    (hne : l.IsChain (· ≠ ·)) :
    l.IsChain (· ⊂ ·) := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton A => simp
  | cons_cons A B tail ih ih₂ =>
      have hs := List.isChain_cons_cons.mp hsub
      have hn := List.isChain_cons_cons.mp hne
      apply List.isChain_cons_cons.mpr
      exact ⟨Finset.ssubset_iff_subset_ne.mpr ⟨hs.1, hn.1⟩,
        ih₂ B hs.2 hn.2⟩

private theorem compressed_weak_chain
    {γ : Type*} [DecidableEq γ]
    {F : Family γ} {c : List (Finset γ)}
    (hne : c ≠ [])
    (hmem : ∀ A ∈ c, A ∈ F)
    (hmono : c.Pairwise (· ⊆ ·)) :
    IsStrictChainIn F (c.destutter (· ≠ ·)) ∧
      (c.destutter (· ≠ ·)).length = strictChangeCount c + 1 := by
  let d := c.destutter (· ≠ ·)
  have hsub : List.Sublist d c := List.destutter_sublist (· ≠ ·) c
  have hdne : d ≠ [] := by
    simpa [d, List.destutter_eq_nil] using hne
  have hpairSub : d.Pairwise (· ⊆ ·) :=
    List.Pairwise.sublist hsub hmono
  have hchainNe : d.IsChain (· ≠ ·) :=
    List.isChain_destutter (· ≠ ·) c
  have hchainSub : d.IsChain (· ⊆ ·) :=
    List.isChain_iff_pairwise.mpr hpairSub
  have hchainStrict : d.IsChain (· ⊂ ·) :=
    isChain_ssubset_of_subset_of_ne d hchainSub hchainNe
  have hdchain : IsStrictChainIn F d := by
    rw [isStrictChainIn_iff_forall_mem_and_isChain]
    refine ⟨?_, hchainStrict⟩
    intro A hAd
    exact hmem A (hsub.subset hAd)
  refine ⟨hdchain, ?_⟩
  rw [strictChangeCount_eq_compress_length_sub_one]
  change d.length = d.length - 1 + 1
  have hpos : 0 < d.length := List.length_pos_iff.mpr hdne
  omega

theorem strictChangeCount_lt_of_isKSperner
    {γ : Type*} [DecidableEq γ]
    {k : Nat} {F : Family γ} {c : List (Finset γ)}
    (hk : IsKSperner k F)
    (hne : c ≠ [])
    (hmem : ∀ A ∈ c, A ∈ F)
    (hmono : c.Pairwise (· ⊆ ·)) :
    strictChangeCount c < k := by
  rcases compressed_weak_chain hne hmem hmono with ⟨hdchain, hlen⟩
  have hexists :
      HasStrictChainLength (strictChangeCount c + 1) F :=
    (hasStrictChainLength_iff_exists_list _ _).mpr
      ⟨c.destutter (· ≠ ·), hlen, hdchain⟩
  by_contra hnot
  have hle : k + 1 ≤ strictChangeCount c + 1 := by omega
  exact hk (hasStrictChainLength_of_le hle hexists)

private theorem exists_false_true_adjacent
    {γ : Type*} (P : γ → Prop) [DecidablePred P]
    {x : γ} {tail : List γ}
    (hx : ¬ P x) (hex : ∃ y ∈ tail, P y) :
    ∃ pre a b post,
      x :: tail = pre ++ a :: b :: post ∧ ¬ P a ∧ P b := by
  induction tail generalizing x with
  | nil => simp at hex
  | cons y ys ih =>
      by_cases hy : P y
      · exact ⟨[], x, y, ys, by simp, hx, hy⟩
      · have hexys : ∃ z ∈ ys, P z := by
          rcases hex with ⟨z, hz, hPz⟩
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact False.elim (hy hPz)
          · exact ⟨z, hz, hPz⟩
        rcases ih hy hexys with ⟨pre, a, b, post, heq, ha, hb⟩
        exact ⟨x :: pre, a, b, post, by simp [heq], ha, hb⟩

private theorem simultaneousChangeCount_pos_of_split
    {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (pre : List (γ × δ)) (p q : γ × δ) (tail : List (γ × δ))
    (h₁ : p.1 ≠ q.1) (h₂ : p.2 ≠ q.2) :
    0 < simultaneousChangeCount (pre ++ p :: q :: tail) := by
  induction pre with
  | nil => simp [simultaneousChangeCount, h₁, h₂]
  | cons r rest ih =>
      cases rest with
      | nil =>
          simp only [List.cons_append, List.nil_append,
            simultaneousChangeCount]
          by_cases h : r.1 ≠ p.1 ∧ r.2 ≠ p.2
          · simp [h, h₁, h₂]
          · simp [h, h₁, h₂]
      | cons s more =>
          simp only [List.cons_append, simultaneousChangeCount]
          by_cases h : r.1 ≠ s.1 ∧ r.2 ≠ s.2
          · simp [h]
          · simpa [h] using ih

private theorem compose_member_left_mem
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    {S : Finset (α ⊕ β)}
    (hS : S ∈ composeFamilies F₁ H₁ F₂ H₂) :
    leftProjection S ∈ F₁ := by
  rcases mem_composeFamilies.mp hS with hsmall | hlarge
  · exact smallPart_subset _ _ hsmall.1
  · exact largePart_subset _ _ hlarge.1

private theorem compose_member_right_mem
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    {S : Finset (α ⊕ β)}
    (hS : S ∈ composeFamilies F₁ H₁ F₂ H₂) :
    rightProjection S ∈ F₂ := by
  rcases mem_composeFamilies.mp hS with hsmall | hlarge
  · exact smallPart_subset _ _ hsmall.2
  · exact largePart_subset _ _ hlarge.2

private theorem sumAtom_not_subset_of_small_pair
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hH₁ : H₁.Nonempty)
    {S : Finset (α ⊕ β)}
    (hsmall : leftProjection S ∈ SmallPart F₁ H₁ ∧
      rightProjection S ∈ SmallPart F₂ H₂) :
    ¬ sumSubset H₁ H₂ ⊆ S := by
  rcases hH₁ with ⟨a, ha⟩
  intro hsub
  have haS : Sum.inl a ∈ S := hsub (inl_mem_sumSubset.mpr ha)
  exact (Finset.disjoint_left.mp (mem_smallPart.mp hsmall.1).2)
    (by simpa [leftProjection] using haS) ha

private theorem sumAtom_subset_of_large_pair
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    {S : Finset (α ⊕ β)}
    (hlarge : leftProjection S ∈ LargePart F₁ H₁ ∧
      rightProjection S ∈ LargePart F₂ H₂) :
    sumSubset H₁ H₂ ⊆ S := by
  intro x hx
  cases x with
  | inl a =>
      have ha := (mem_largePart.mp hlarge.1).2 (inl_mem_sumSubset.mp hx)
      simpa [leftProjection] using ha
  | inr b =>
      have hb := (mem_largePart.mp hlarge.2).2 (inr_mem_sumSubset.mp hx)
      simpa [rightProjection] using hb

private theorem simultaneous_transition_of_compressed_endpoint_chain
    [Fintype α] [Fintype β]
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (hH₁ : H₁.Nonempty) (hH₂ : H₂.Nonempty)
    {d : List (Finset (α ⊕ β))}
    (hdchain : IsStrictChainIn (composeFamilies F₁ H₁ F₂ H₂) d)
    (hempty : (∅ : Finset (α ⊕ β)) ∈ d)
    (huniv : (Finset.univ : Finset (α ⊕ β)) ∈ d) :
    ∃ pre A B post,
      d = pre ++ A :: B :: post ∧
      leftProjection A ≠ leftProjection B ∧
      rightProjection A ≠ rightProjection B := by
  have hdPair : d.Pairwise (· ⊂ ·) :=
    IsStrictChainIn.pairwise_ssubset hdchain
  have hdne : d ≠ [] := by
    exact List.ne_nil_of_mem hempty
  rcases hdform : d with _ | ⟨D, tail⟩
  · exact False.elim (hdne hdform)
  have hDempty : D = ∅ := by
    by_contra hne
    have hemtail : (∅ : Finset (α ⊕ β)) ∈ tail := by
      have := hempty
      rw [hdform] at this
      have hemptyD : (∅ : Finset (α ⊕ β)) ≠ D := Ne.symm hne
      simpa [hemptyD] using this
    have hDsub := (List.pairwise_cons.mp (by simpa [hdform] using hdPair)).1
      (∅ : Finset (α ⊕ β)) hemtail
    simpa using hDsub
  subst D
  have hsumne : (sumSubset H₁ H₂).Nonempty :=
    sumAtom_nonempty_left hH₁
  have hground : Nonempty (α ⊕ β) := by
    rcases hsumne with ⟨x, hx⟩
    exact ⟨x⟩
  letI : Nonempty (α ⊕ β) := hground
  have hunivne :
      (Finset.univ : Finset (α ⊕ β)) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp Finset.univ_nonempty
  have hunivtail :
      (Finset.univ : Finset (α ⊕ β)) ∈ tail := by
    have := huniv
    rw [hdform] at this
    simpa [hunivne] using this
  let P : Finset (α ⊕ β) → Prop := fun S => sumSubset H₁ H₂ ⊆ S
  have hPempty : ¬ P (∅ : Finset (α ⊕ β)) := by
    intro h
    rcases hsumne with ⟨x, hx⟩
    simpa [P] using h hx
  have hex : ∃ S ∈ tail, P S :=
    ⟨Finset.univ, hunivtail, by simp [P]⟩
  rcases exists_false_true_adjacent P hPempty hex with
    ⟨pre, A, B, post, heq, hPA, hPB⟩
  have hdmem : ∀ S ∈ d, S ∈ composeFamilies F₁ H₁ F₂ H₂ :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hdchain |>.1
  have hAd : A ∈ d := by
    rw [hdform, heq]
    simp
  have hBd : B ∈ d := by
    rw [hdform, heq]
    simp
  have hAG := hdmem A hAd
  have hBG := hdmem B hBd
  have hAsmall :
      leftProjection A ∈ SmallPart F₁ H₁ ∧
        rightProjection A ∈ SmallPart F₂ H₂ := by
    rcases mem_composeFamilies.mp hAG with hsmall | hlarge
    · exact hsmall
    · exact False.elim (hPA (sumAtom_subset_of_large_pair hlarge))
  have hBlarge :
      leftProjection B ∈ LargePart F₁ H₁ ∧
        rightProjection B ∈ LargePart F₂ H₂ := by
    rcases mem_composeFamilies.mp hBG with hsmall | hlarge
    · exact False.elim
        (sumAtom_not_subset_of_small_pair hH₁ hsmall hPB)
    · exact hlarge
  have hleft : leftProjection A ≠ leftProjection B := by
    intro heqLeft
    rcases hH₁ with ⟨a, ha⟩
    have haB := (mem_largePart.mp hBlarge.1).2 ha
    have haA : a ∈ leftProjection A := by simpa [heqLeft] using haB
    exact (Finset.disjoint_left.mp (mem_smallPart.mp hAsmall.1).2) haA ha
  have hright : rightProjection A ≠ rightProjection B := by
    intro heqRight
    rcases hH₂ with ⟨b, hb⟩
    have hbB := (mem_largePart.mp hBlarge.2).2 hb
    have hbA : b ∈ rightProjection A := by simpa [heqRight] using hbB
    exact (Finset.disjoint_left.mp (mem_smallPart.mp hAsmall.2).2) hbA hb
  exact ⟨pre, A, B, post, by simpa [hdform] using heq,
    hleft, hright⟩

/-- The simultaneous small-to-large transition gives the sharp projected
change bound used in MNS Lemma 18. -/
theorem compose_chainFree
    [Fintype α] [Fintype β]
    {k₁ k₂ : Nat}
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (h₁ : IsSaturatedKSperner k₁ F₁)
    (h₂ : IsSaturatedKSperner k₂ F₂)
    (hend₁ : HasEndpoints F₁) (hend₂ : HasEndpoints F₂)
    (hH₁ : IsHomogeneousAtom F₁ H₁)
    (hH₂ : IsHomogeneousAtom F₂ H₂) :
    IsKSperner (k₁ + k₂ - 2)
      (composeFamilies F₁ H₁ F₂ H₂) := by
  have hk₁ : 2 ≤ k₁ :=
    two_le_of_saturated_endpoints_homogeneous h₁ hend₁ hH₁
  have hk₂ : 2 ≤ k₂ :=
    two_le_of_saturated_endpoints_homogeneous h₂ hend₂ hH₂
  intro hforbidden
  rcases (hasStrictChainLength_iff_exists_list _ _).mp hforbidden with
    ⟨c, hclen, hc⟩
  have hcmem : ∀ S ∈ c, S ∈ composeFamilies F₁ H₁ F₂ H₂ :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hc |>.1
  have hcPairStrict : c.Pairwise (· ⊂ ·) :=
    IsStrictChainIn.pairwise_ssubset hc
  have hcPairSub : c.Pairwise (· ⊆ ·) :=
    hcPairStrict.imp fun h => h.le
  have hcChainNe : c.IsChain (· ≠ ·) :=
    ((isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hc |>.2).imp
      fun {A B} hAB => hAB.ne
  let w : List (Finset (α ⊕ β)) :=
    (∅ : Finset (α ⊕ β)) :: c ++ [Finset.univ]
  have hwne : w ≠ [] := by simp [w]
  have hwmem : ∀ S ∈ w, S ∈ composeFamilies F₁ H₁ F₂ H₂ := by
    intro S hS
    change S ∈ ((∅ : Finset (α ⊕ β)) :: c) ++ [Finset.univ] at hS
    rw [List.mem_append] at hS
    rcases hS with hprefix | hlast
    · rw [List.mem_cons] at hprefix
      rcases hprefix with rfl | hSc
      · exact (compose_hasEndpoints hend₁ hend₂).1
      · exact hcmem S hSc
    · have hEq : S = (Finset.univ : Finset (α ⊕ β)) := by
        simpa using hlast
      subst S
      exact (compose_hasEndpoints hend₁ hend₂).2
  have hwPair : w.Pairwise (· ⊆ ·) := by
    rw [show w = (∅ : Finset (α ⊕ β)) :: (c ++ [Finset.univ]) by rfl,
      List.pairwise_cons]
    constructor
    · intro S hS
      simp
    · rw [List.pairwise_append]
      refine ⟨hcPairSub, by simp, ?_⟩
      intro S hS T hT
      simp at hT
      subst T
      simp
  let d := w.destutter (· ≠ ·)
  rcases compressed_weak_chain hwne hwmem hwPair with
    ⟨hdchain, hdlen⟩
  have hdchainD :
      IsStrictChainIn (composeFamilies F₁ H₁ F₂ H₂) d := by
    simpa [d] using hdchain
  have hwdedup : d = w.dedup := by
    exact hwPair.destutter_eq_dedup
  have hempty : (∅ : Finset (α ⊕ β)) ∈ d := by
    rw [hwdedup]
    simp [w]
  have huniv : (Finset.univ : Finset (α ⊕ β)) ∈ d := by
    rw [hwdedup]
    simp [w]
  have hH₁ne : H₁.Nonempty :=
    Finset.card_pos.mp (by have := hH₁.2; omega)
  have hH₂ne : H₂.Nonempty :=
    Finset.card_pos.mp (by have := hH₂.2; omega)
  rcases simultaneous_transition_of_compressed_endpoint_chain
      (F₁ := F₁) (H₁ := H₁) (F₂ := F₂) (H₂ := H₂)
      hH₁ne hH₂ne hdchainD hempty huniv with
    ⟨pre, A, B, post, hdSplit, hleft, hright⟩
  let projPair : Finset (α ⊕ β) → Finset α × Finset β := fun S =>
    (leftProjection S, rightProjection S)
  let p := d.map projPair
  have hpSplit :
      p = pre.map projPair ++ projPair A :: projPair B :: post.map projPair := by
    simp [p, hdSplit, projPair]
  have hsim : 0 < simultaneousChangeCount p := by
    rw [hpSplit]
    exact simultaneousChangeCount_pos_of_split _ _ _ _ hleft hright
  have hdChainStrict : d.IsChain (· ⊂ ·) :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hdchainD |>.2
  have hpChainNe : p.IsChain (· ≠ ·) := by
    change (d.map projPair).IsChain (· ≠ ·)
    rw [List.isChain_map]
    exact hdChainStrict.imp fun {S T} hST hEq =>
      hST.ne (projections_injective hEq)
  have hpCount : strictChangeCount p = p.length - 1 :=
    strictChangeCount_eq_length_sub_one_of_chain p hpChainNe
  have hpne : p ≠ [] := by
    simp [p, List.ne_nil_of_mem hempty]
  have hplenpos : 0 < p.length := List.length_pos_iff.mpr hpne
  have hcountLower :
      d.length ≤
        strictChangeCount (d.map leftProjection) +
          strictChangeCount (d.map rightProjection) := by
    have hid := pair_change_count_identity p
    have hplen : p.length = d.length := by simp [p]
    have hleftMap : p.map Prod.fst = d.map leftProjection := by
      simp [p, projPair, Function.comp_def]
    have hrightMap : p.map Prod.snd = d.map rightProjection := by
      simp [p, projPair, Function.comp_def]
    rw [hleftMap, hrightMap] at hid
    omega
  have hdne : d ≠ [] := List.ne_nil_of_mem hempty
  have hdPairSub : d.Pairwise (· ⊆ ·) :=
    (IsStrictChainIn.pairwise_ssubset hdchainD).imp fun h => h.le
  have hleftNe : d.map leftProjection ≠ [] := by simp [hdne]
  have hrightNe : d.map rightProjection ≠ [] := by simp [hdne]
  have hleftMem : ∀ A ∈ d.map leftProjection, A ∈ F₁ := by
    intro A hA
    rcases List.mem_map.mp hA with ⟨S, hSd, rfl⟩
    have hSG := (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp
      hdchainD |>.1 S hSd
    exact compose_member_left_mem hSG
  have hrightMem : ∀ B ∈ d.map rightProjection, B ∈ F₂ := by
    intro B hB
    rcases List.mem_map.mp hB with ⟨S, hSd, rfl⟩
    have hSG := (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp
      hdchainD |>.1 S hSd
    exact compose_member_right_mem hSG
  have hleftPair : (d.map leftProjection).Pairwise (· ⊆ ·) :=
    hdPairSub.map leftProjection fun _ _ h => leftProjection_mono h
  have hrightPair : (d.map rightProjection).Pairwise (· ⊆ ·) :=
    hdPairSub.map rightProjection fun _ _ h => rightProjection_mono h
  have hleftUpper : strictChangeCount (d.map leftProjection) < k₁ :=
    strictChangeCount_lt_of_isKSperner h₁.1 hleftNe hleftMem hleftPair
  have hrightUpper : strictChangeCount (d.map rightProjection) < k₂ :=
    strictChangeCount_lt_of_isKSperner h₂.1 hrightNe hrightMem hrightPair
  have hcSubW : List.Sublist c w := by
    have h₁sub : List.Sublist c (c ++ [Finset.univ]) := by
      simpa using (List.Sublist.append (List.Sublist.refl c)
        (List.Sublist.slnil : List.Sublist [] [Finset.univ]))
    exact h₁sub.cons (∅ : Finset (α ⊕ β))
  have hclenD : c.length ≤ d.length := by
    exact hcChainNe.length_le_length_destutter_ne hcSubW
  omega

/-! ## Partial-atom chain splits -/

/-- The factor chain obtained from a partial-atom true-through witness, split
into its nonempty small and large segments. -/
structure PartialAtomChainSplit
    {γ : Type*} [DecidableEq γ] [Fintype γ]
    (k : Nat) (F : Family γ) (H S : Finset γ) where
  lower : List (Finset γ)
  upper : List (Finset γ)
  lower_nonempty : lower ≠ []
  upper_nonempty : upper ≠ []
  length_add : lower.length + upper.length = k
  lower_chain : IsStrictChainIn (SmallPart F H) lower
  upper_chain : IsStrictChainIn (LargePart F H) upper
  lower_le_original : ∀ A, A ∈ lower → A ⊆ S
  original_le_upper : ∀ A, A ∈ upper → S ⊆ A

private theorem maximal_factor_chain_contains_endpoints
    {γ : Type*} [DecidableEq γ] [Fintype γ]
    {k : Nat} {F : Family γ} {d : List (Finset γ)}
    (hk : 0 < k)
    (hsp : IsKSperner k F)
    (hend : HasEndpoints F)
    (hd : IsStrictChainIn F d)
    (hlen : d.length = k) :
    (∅ : Finset γ) ∈ d ∧ Finset.univ ∈ d := by
  have hdmem : ∀ A ∈ d, A ∈ F :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hd |>.1
  have hdPair : d.Pairwise (· ⊂ ·) :=
    IsStrictChainIn.pairwise_ssubset hd
  have hdne : d ≠ [] := by
    intro hzero
    rw [hzero] at hlen
    simp at hlen
    omega
  have hempty : (∅ : Finset γ) ∈ d := by
    by_contra hnot
    let c := (∅ : Finset γ) :: d
    have hcPair : c.Pairwise (· ⊂ ·) := by
      rw [show c = (∅ : Finset γ) :: d by rfl, List.pairwise_cons]
      refine ⟨?_, hdPair⟩
      intro A hAd
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨by simp, ?_⟩
      intro hEq
      apply hnot
      simpa [hEq] using hAd
    have hcChain : IsStrictChainIn F c := by
      rw [isStrictChainIn_iff_forall_mem_and_isChain]
      refine ⟨?_, List.isChain_iff_pairwise.mpr hcPair⟩
      intro A hAc
      rw [show c = (∅ : Finset γ) :: d by rfl, List.mem_cons] at hAc
      rcases hAc with rfl | hAd
      · exact hend.1
      · exact hdmem A hAd
    have hlong : HasStrictChainLength (k + 1) F :=
      (hasStrictChainLength_iff_exists_list _ _).mpr
        ⟨c, by simp [c, hlen], hcChain⟩
    exact hsp hlong
  have huniv : (Finset.univ : Finset γ) ∈ d := by
    by_contra hnot
    let c := d ++ [Finset.univ]
    have hcPair : c.Pairwise (· ⊂ ·) := by
      rw [show c = d ++ [Finset.univ] by rfl, List.pairwise_append]
      refine ⟨hdPair, by simp, ?_⟩
      intro A hAd B hB
      have hBuniv : B = (Finset.univ : Finset γ) := by simpa using hB
      subst B
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨by simp, ?_⟩
      intro hEq
      apply hnot
      simpa [hEq] using hAd
    have hcChain : IsStrictChainIn F c := by
      rw [isStrictChainIn_iff_forall_mem_and_isChain]
      refine ⟨?_, List.isChain_iff_pairwise.mpr hcPair⟩
      intro A hAc
      rw [show c = d ++ [Finset.univ] by rfl, List.mem_append] at hAc
      rcases hAc with hAd | hAu
      · exact hdmem A hAd
      · have hEq : A = (Finset.univ : Finset γ) := by simpa using hAu
        subst A
        exact hend.2
    have hlong : HasStrictChainLength (k + 1) F :=
      (hasStrictChainLength_iff_exists_list _ _).mpr
        ⟨c, by simp [c, hlen], hcChain⟩
    exact hsp hlong
  exact ⟨hempty, huniv⟩

private theorem comparable_filter_length_add
    {γ : Type*} [DecidableEq γ]
    (d : List (Finset γ)) (T : Finset γ)
    (hcomp : ∀ U ∈ d, U ⊂ T ∨ T ⊂ U) :
    (d.filter fun U => decide (U ⊂ T)).length +
        (d.filter fun U => decide (T ⊂ U)).length = d.length := by
  induction d with
  | nil => simp
  | cons U tail ih =>
      have hU := hcomp U (by simp)
      have htail : ∀ V ∈ tail, V ⊂ T ∨ T ⊂ V := by
        intro V hV
        exact hcomp V (by simp [hV])
      have ht := ih htail
      rcases hU with hUT | hTU
      · have hnTU : ¬ T ⊂ U := fun h => lt_asymm hUT h
        simp [hUT, hnTU]
        omega
      · have hnUT : ¬ U ⊂ T := fun h => lt_asymm hTU h
        simp [hTU, hnUT]
        omega

/-- Factor saturation plus endpoint completion supplies the exact lower/upper
split needed by the composition staircase. -/
theorem exists_partialAtomChainSplit
    {γ : Type*} [DecidableEq γ] [Fintype γ]
    {k : Nat} {F : Family γ} {H S : Finset γ}
    (hsat : IsSaturatedKSperner k F)
    (hend : HasEndpoints F)
    (hH : IsHomogeneousAtom F H) :
    Nonempty (PartialAtomChainSplit k F H S) := by
  have hcard := hH.2
  have hone : 1 < H.card := by omega
  rcases Finset.one_lt_card.mp hone with ⟨x, hxH, y, hyH, hxy⟩
  have hyx : y ≠ x := hxy.symm
  let T := partialAtomSet S H x
  have hTF : T ∉ F :=
    partialAtomSet_not_mem_of_atomBlock hH.1.1 hxH hyH hyx
  rcases ((isSaturatedKSperner_iff_hasStrictChainThrough k F).mp hsat).2
      T hTF with ⟨c, hc⟩
  rcases erase_inserted_of_strictChainWitness hTF hc with
    ⟨hdlen, hdchain, hdmemErase, hdcomp⟩
  let d := c.erase T
  have hdlen' : d.length = k := by simpa [d] using hdlen
  have hdchain' : IsStrictChainIn F d := by simpa [d] using hdchain
  have hk₂ : 2 ≤ k :=
    two_le_of_saturated_endpoints_homogeneous hsat hend hH
  have hendd := maximal_factor_chain_contains_endpoints
    (k := k) (F := F) (d := d) (by omega) hsat.1 hend hdchain' hdlen'
  let lower := d.filter fun U => decide (U ⊂ T)
  let upper := d.filter fun U => decide (T ⊂ U)
  have hdall : ∀ U ∈ d, U ∈ F :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hdchain' |>.1
  have hlmem : ∀ U ∈ lower, U ∈ SmallPart F H := by
    intro U hUl
    have hfilter : U ∈ d ∧ U ⊂ T := by simpa [lower] using hUl
    have hUd : U ∈ d := hfilter.1
    have hUT : U ⊂ T := hfilter.2
    have hUF := hdall U hUd
    rcases hH.1.1 U hUF with hsmall | hlarge
    · exact mem_smallPart.mpr ⟨hUF, hsmall⟩
    · exact False.elim
        (partialAtomSet_not_superset hyH hyx (hlarge.trans hUT.le))
  have humem : ∀ U ∈ upper, U ∈ LargePart F H := by
    intro U hUu
    have hfilter : U ∈ d ∧ T ⊂ U := by simpa [upper] using hUu
    have hUd : U ∈ d := hfilter.1
    have hTU : T ⊂ U := hfilter.2
    have hUF := hdall U hUd
    rcases hH.1.1 U hUF with hsmall | hlarge
    · have hxT : x ∈ T := by simp [T, partialAtomSet]
      have hxU : x ∈ U := hTU.le hxT
      exact False.elim ((Finset.disjoint_left.mp hsmall) hxU hxH)
    · exact mem_largePart.mpr ⟨hUF, hlarge⟩
  have hlchain : IsStrictChainIn (SmallPart F H) lower := by
    rw [isStrictChainIn_iff_forall_mem_and_isChain]
    refine ⟨hlmem, ?_⟩
    have hrel := (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp
      hdchain' |>.2
    exact hrel.sublist (by simpa [lower] using
      (List.filter_sublist :
        List.Sublist (d.filter fun U => decide (U ⊂ T)) d))
  have huchain : IsStrictChainIn (LargePart F H) upper := by
    rw [isStrictChainIn_iff_forall_mem_and_isChain]
    refine ⟨humem, ?_⟩
    have hrel := (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp
      hdchain' |>.2
    exact hrel.sublist (by simpa [upper] using
      (List.filter_sublist :
        List.Sublist (d.filter fun U => decide (T ⊂ U)) d))
  have hTne : T ≠ ∅ := by
    intro hzero
    have hxT : x ∈ T := by simp [T, partialAtomSet]
    simpa [hzero] using hxT
  have hemptyT : (∅ : Finset γ) ⊂ T :=
    Finset.ssubset_iff_subset_ne.mpr ⟨by simp, Ne.symm hTne⟩
  have hTneUniv : T ≠ (Finset.univ : Finset γ) := by
    intro hfull
    have hyT : y ∈ T := by simp [hfull]
    simpa [T, partialAtomSet, hyH, hyx] using hyT
  have hTuniv : T ⊂ (Finset.univ : Finset γ) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨by simp, hTneUniv⟩
  have hemptyLower : (∅ : Finset γ) ∈ lower := by
    simp [lower, hendd.1, hemptyT]
  have hunivUpper : (Finset.univ : Finset γ) ∈ upper := by
    simp [upper, hendd.2, hTuniv]
  have hlne : lower ≠ [] := List.ne_nil_of_mem hemptyLower
  have hune : upper ≠ [] := List.ne_nil_of_mem hunivUpper
  have hcompAll : ∀ U ∈ d, U ⊂ T ∨ T ⊂ U := by
    intro U hUd
    have hUc : U ∈ c.erase T := by simpa [d] using hUd
    exact hdcomp U hUc
  have hlength : lower.length + upper.length = k := by
    have hparts := comparable_filter_length_add d T hcompAll
    simpa [lower, upper, hdlen'] using hparts
  have hlowerOriginal : ∀ U, U ∈ lower → U ⊆ S := by
    intro U hUl
    have hfilter : U ∈ d ∧ U ⊂ T := by simpa [lower] using hUl
    have hUT : U ⊂ T := hfilter.2
    have hsmall := mem_smallPart.mp (hlmem U hUl) |>.2
    exact subset_original_of_disjoint_of_subset_partialAtomSet
      hxH hsmall hUT.le
  have horiginalUpper : ∀ U, U ∈ upper → S ⊆ U := by
    intro U hUu
    have hfilter : U ∈ d ∧ T ⊂ U := by simpa [upper] using hUu
    have hTU : T ⊂ U := hfilter.2
    have hlarge := mem_largePart.mp (humem U hUu) |>.2
    exact original_subset_of_atom_subset_of_partialAtomSet_subset
      hlarge hTU.le
  exact ⟨⟨lower, upper, hlne, hune, hlength, hlchain, huchain,
    hlowerOriginal, horiginalUpper⟩⟩

/-! ## Staircase interleaving and saturation -/

/-- Walk through the left chain while holding the right head fixed, then
through the right tail while holding the left last member fixed. -/
def staircaseSum
    {γ δ : Type*} [DecidableEq γ] [DecidableEq δ] :
    List (Finset γ) → List (Finset δ) → List (Finset (γ ⊕ δ))
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
      (x :: xs).map (fun A => sumSubset A y) ++
        ys.map (fun B =>
          sumSubset ((x :: xs).getLast (by simp)) B)

theorem staircaseSum_length
    {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (xs : List (Finset γ)) (ys : List (Finset δ))
    (hx : xs ≠ []) (hy : ys ≠ []) :
    (staircaseSum xs ys).length = xs.length + ys.length - 1 := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons x xt =>
      cases ys with
      | nil => exact False.elim (hy rfl)
      | cons y yt =>
          simp [staircaseSum]
          omega

theorem staircaseSum_chain
    {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    {F : Family γ} {G : Family δ}
    {xs : List (Finset γ)} {ys : List (Finset δ)}
    (hxs : IsStrictChainIn F xs)
    (hys : IsStrictChainIn G ys)
    (hx : xs ≠ []) (hy : ys ≠ []) :
    IsStrictChainIn (productFamily F G) (staircaseSum xs ys) := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons x xt =>
      cases ys with
      | nil => exact False.elim (hy rfl)
      | cons y yt =>
          let xlast := (x :: xt).getLast (by simp)
          have hxmem : ∀ A ∈ x :: xt, A ∈ F :=
            (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hxs |>.1
          have hymem : ∀ B ∈ y :: yt, B ∈ G :=
            (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hys |>.1
          have hxPair : (x :: xt).Pairwise (· ⊂ ·) :=
            IsStrictChainIn.pairwise_ssubset hxs
          have hyPair : (y :: yt).Pairwise (· ⊂ ·) :=
            IsStrictChainIn.pairwise_ssubset hys
          have hxPairSub : (x :: xt).Pairwise (· ⊆ ·) :=
            hxPair.imp fun h => h.le
          have hxlastMem : xlast ∈ F := by
            exact hxmem xlast (List.getLast_mem (by simp))
          rw [isStrictChainIn_iff_forall_mem_and_isChain]
          constructor
          · intro S hS
            simp only [staircaseSum, List.mem_append, List.mem_map] at hS
            rcases hS with ⟨A, hA, rfl⟩ | ⟨B, hB, rfl⟩
            · apply mem_productFamily.mpr
              simp
              exact ⟨hxmem A hA, hymem y (by simp)⟩
            · apply mem_productFamily.mpr
              simp
              exact ⟨hxlastMem, hymem B (by simp [hB])⟩
          · simp only [staircaseSum]
            rw [List.isChain_iff_pairwise, List.pairwise_append]
            refine ⟨?_, ?_, ?_⟩
            · exact hxPair.map (fun A => sumSubset A y) fun _ _ h =>
                sumSubset_ssubset_control.mpr
                  (Or.inl ⟨h, by simp⟩)
            · have hytail : yt.Pairwise (· ⊂ ·) :=
                (List.pairwise_cons.mp hyPair).2
              exact hytail.map (fun B => sumSubset xlast B) fun _ _ h =>
                sumSubset_ssubset_control.mpr
                  (Or.inr ⟨by simp, h⟩)
            · intro U hU V hV
              rcases List.mem_map.mp hU with ⟨A, hA, rfl⟩
              rcases List.mem_map.mp hV with ⟨B, hB, rfl⟩
              have hAxlast : A ⊆ xlast := hxPairSub.rel_getLast hA
              have hyB : y ⊂ B :=
                (List.pairwise_cons.mp hyPair).1 B hB
              exact sumSubset_ssubset_control.mpr
                (Or.inr ⟨hAxlast, hyB⟩)

private theorem staircaseSum_subset_sumSubset
    {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    {xs : List (Finset γ)} {ys : List (Finset δ)}
    {Sγ : Finset γ} {Sδ : Finset δ}
    (hx : xs ≠ []) (hy : ys ≠ [])
    (hxs : ∀ A ∈ xs, A ⊆ Sγ)
    (hys : ∀ B ∈ ys, B ⊆ Sδ) :
    ∀ U ∈ staircaseSum xs ys, U ⊆ sumSubset Sγ Sδ := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons x xt =>
      cases ys with
      | nil => exact False.elim (hy rfl)
      | cons y yt =>
          intro U hU
          simp only [staircaseSum, List.mem_append, List.mem_map] at hU
          rcases hU with ⟨A, hA, rfl⟩ | ⟨B, hB, rfl⟩
          · exact sumSubset_subset_iff.mpr
              ⟨hxs A hA, hys y (by simp)⟩
          · exact sumSubset_subset_iff.mpr
              ⟨hxs _ (List.getLast_mem (by simp)),
                hys B (by simp [hB])⟩

private theorem sumSubset_subset_staircaseSum
    {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    {xs : List (Finset γ)} {ys : List (Finset δ)}
    {Sγ : Finset γ} {Sδ : Finset δ}
    (hx : xs ≠ []) (hy : ys ≠ [])
    (hxs : ∀ A ∈ xs, Sγ ⊆ A)
    (hys : ∀ B ∈ ys, Sδ ⊆ B) :
    ∀ U ∈ staircaseSum xs ys, sumSubset Sγ Sδ ⊆ U := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons x xt =>
      cases ys with
      | nil => exact False.elim (hy rfl)
      | cons y yt =>
          intro U hU
          simp only [staircaseSum, List.mem_append, List.mem_map] at hU
          rcases hU with ⟨A, hA, rfl⟩ | ⟨B, hB, rfl⟩
          · exact sumSubset_subset_iff.mpr
              ⟨hxs A hA, hys y (by simp)⟩
          · exact sumSubset_subset_iff.mpr
              ⟨hxs _ (List.getLast_mem (by simp)),
                hys B (by simp [hB])⟩

/-- Every external set is inserted between the two nonempty factor
staircases, producing the exact source-length through-chain. -/
theorem compose_external_chain_through
    [Fintype α] [Fintype β]
    {k₁ k₂ : Nat}
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (h₁ : IsSaturatedKSperner k₁ F₁)
    (h₂ : IsSaturatedKSperner k₂ F₂)
    (hend₁ : HasEndpoints F₁) (hend₂ : HasEndpoints F₂)
    (hH₁ : IsHomogeneousAtom F₁ H₁)
    (hH₂ : IsHomogeneousAtom F₂ H₂)
    {S : Finset (α ⊕ β)}
    (hS : S ∉ composeFamilies F₁ H₁ F₂ H₂) :
    HasStrictChainThrough (k₁ + k₂ - 1)
      (insert S (composeFamilies F₁ H₁ F₂ H₂)) S := by
  classical
  let S₁ := leftProjection S
  let S₂ := rightProjection S
  let split₁ : PartialAtomChainSplit k₁ F₁ H₁ S₁ :=
    Classical.choice (exists_partialAtomChainSplit h₁ hend₁ hH₁)
  let split₂ : PartialAtomChainSplit k₂ F₂ H₂ S₂ :=
    Classical.choice (exists_partialAtomChainSplit h₂ hend₂ hH₂)
  let lowerPairs := staircaseSum split₁.lower split₂.lower
  let upperPairs := staircaseSum split₁.upper split₂.upper
  have hlchain : IsStrictChainIn
      (productFamily (SmallPart F₁ H₁) (SmallPart F₂ H₂)) lowerPairs := by
    exact staircaseSum_chain split₁.lower_chain split₂.lower_chain
      split₁.lower_nonempty split₂.lower_nonempty
  have huchain : IsStrictChainIn
      (productFamily (LargePart F₁ H₁) (LargePart F₂ H₂)) upperPairs := by
    exact staircaseSum_chain split₁.upper_chain split₂.upper_chain
      split₁.upper_nonempty split₂.upper_nonempty
  have hlmem : ∀ U ∈ lowerPairs,
      U ∈ productFamily (SmallPart F₁ H₁) (SmallPart F₂ H₂) :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp hlchain |>.1
  have humem : ∀ U ∈ upperPairs,
      U ∈ productFamily (LargePart F₁ H₁) (LargePart F₂ H₂) :=
    (isStrictChainIn_iff_forall_mem_and_isChain _ _).mp huchain |>.1
  have hlSub : ∀ U ∈ lowerPairs, U ⊆ S := by
    intro U hU
    rw [← sumSubset_projections S]
    exact staircaseSum_subset_sumSubset
      split₁.lower_nonempty split₂.lower_nonempty
      split₁.lower_le_original split₂.lower_le_original U hU
  have huSub : ∀ U ∈ upperPairs, S ⊆ U := by
    intro U hU
    rw [← sumSubset_projections S]
    exact sumSubset_subset_staircaseSum
      split₁.upper_nonempty split₂.upper_nonempty
      split₁.original_le_upper split₂.original_le_upper U hU
  have hlStrict : ∀ U ∈ lowerPairs, U ⊂ S := by
    intro U hU
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hlSub U hU, ?_⟩
    intro hEq
    apply hS
    rw [← hEq]
    exact mem_composeFamilies.mpr (Or.inl (mem_productFamily.mp (hlmem U hU)))
  have huStrict : ∀ U ∈ upperPairs, S ⊂ U := by
    intro U hU
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨huSub U hU, ?_⟩
    intro hEq
    apply hS
    rw [hEq]
    exact mem_composeFamilies.mpr (Or.inr (mem_productFamily.mp (humem U hU)))
  let c := lowerPairs ++ S :: upperPairs
  have hcChain :
      IsStrictChainIn (insert S (composeFamilies F₁ H₁ F₂ H₂)) c := by
    rw [isStrictChainIn_iff_forall_mem_and_isChain]
    constructor
    · intro U hUc
      rw [show c = lowerPairs ++ S :: upperPairs by rfl,
        List.mem_append] at hUc
      rcases hUc with hUl | hUrest
      · exact Finset.mem_insert_of_mem
          (mem_composeFamilies.mpr
            (Or.inl (mem_productFamily.mp (hlmem U hUl))))
      · rw [List.mem_cons] at hUrest
        rcases hUrest with rfl | hUu
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (mem_composeFamilies.mpr
              (Or.inr (mem_productFamily.mp (humem U hUu))))
    · rw [List.isChain_iff_pairwise]
      change (lowerPairs ++ S :: upperPairs).Pairwise (· ⊂ ·)
      rw [List.pairwise_append]
      refine ⟨IsStrictChainIn.pairwise_ssubset hlchain, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨huStrict, IsStrictChainIn.pairwise_ssubset huchain⟩
      · intro L hLl U hUr
        rw [List.mem_cons] at hUr
        rcases hUr with rfl | hUu
        · exact hlStrict L hLl
        · exact strictSubset_trans (hlStrict L hLl) (huStrict U hUu)
  have hclen : c.length = k₁ + k₂ - 1 := by
    have hllength := staircaseSum_length split₁.lower split₂.lower
      split₁.lower_nonempty split₂.lower_nonempty
    have hulength := staircaseSum_length split₁.upper split₂.upper
      split₁.upper_nonempty split₂.upper_nonempty
    have hlpos : 0 < split₁.lower.length :=
      List.length_pos_iff.mpr split₁.lower_nonempty
    have hlpos₂ : 0 < split₂.lower.length :=
      List.length_pos_iff.mpr split₂.lower_nonempty
    have hupos : 0 < split₁.upper.length :=
      List.length_pos_iff.mpr split₁.upper_nonempty
    have hupos₂ : 0 < split₂.upper.length :=
      List.length_pos_iff.mpr split₂.upper_nonempty
    have hsplit₁ := split₁.length_add
    have hsplit₂ := split₂.length_add
    simp only [c, List.length_append, List.length_cons, List.length_nil]
    dsimp only [lowerPairs, upperPairs]
    omega
  exact ⟨c, hclen, hcChain, by simp [c]⟩

/-- Source-facing MNS Lemma 18.  Both original endpoint assumptions are
explicit, and the natural subtraction is justified internally. -/
theorem compose_saturated
    [Fintype α] [Fintype β]
    {k₁ k₂ : Nat}
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (h₁ : IsSaturatedKSperner k₁ F₁)
    (h₂ : IsSaturatedKSperner k₂ F₂)
    (hend₁ : HasEndpoints F₁) (hend₂ : HasEndpoints F₂)
    (hH₁ : IsHomogeneousAtom F₁ H₁)
    (hH₂ : IsHomogeneousAtom F₂ H₂) :
    IsSaturatedKSperner (k₁ + k₂ - 2)
      (composeFamilies F₁ H₁ F₂ H₂) := by
  have hk₁ : 2 ≤ k₁ :=
    two_le_of_saturated_endpoints_homogeneous h₁ hend₁ hH₁
  have hk₂ : 2 ≤ k₂ :=
    two_le_of_saturated_endpoints_homogeneous h₂ hend₂ hH₂
  refine ⟨compose_chainFree h₁ h₂ hend₁ hend₂ hH₁ hH₂, ?_⟩
  intro S hS
  rcases compose_external_chain_through h₁ h₂ hend₁ hend₂ hH₁ hH₂ hS with
    ⟨c, hlen, hc, hSc⟩
  apply (hasStrictChainLength_iff_exists_list _ _).mpr
  refine ⟨c, ?_, hc⟩
  omega

/-- Full reusable composition package, including all source-facing structural
and exact-cardinality conclusions. -/
theorem compose_full
    [Fintype α] [Fintype β]
    {k₁ k₂ : Nat}
    {F₁ : Family α} {H₁ : Finset α}
    {F₂ : Family β} {H₂ : Finset β}
    (h₁ : IsSaturatedKSperner k₁ F₁)
    (h₂ : IsSaturatedKSperner k₂ F₂)
    (hend₁ : HasEndpoints F₁) (hend₂ : HasEndpoints F₂)
    (hH₁ : IsHomogeneousAtom F₁ H₁)
    (hH₂ : IsHomogeneousAtom F₂ H₂) :
    2 ≤ k₁ ∧ 2 ≤ k₂ ∧
      IsSaturatedKSperner (k₁ + k₂ - 2)
        (composeFamilies F₁ H₁ F₂ H₂) ∧
      HasEndpoints (composeFamilies F₁ H₁ F₂ H₂) ∧
      IsHomogeneousAtom (composeFamilies F₁ H₁ F₂ H₂)
        (sumSubset H₁ H₂) ∧
      SmallPart (composeFamilies F₁ H₁ F₂ H₂) (sumSubset H₁ H₂) =
        productFamily (SmallPart F₁ H₁) (SmallPart F₂ H₂) ∧
      LargePart (composeFamilies F₁ H₁ F₂ H₂) (sumSubset H₁ H₂) =
        productFamily (LargePart F₁ H₁) (LargePart F₂ H₂) ∧
      (composeFamilies F₁ H₁ F₂ H₂).card =
        (SmallPart F₁ H₁).card * (SmallPart F₂ H₂).card +
        (LargePart F₁ H₁).card * (LargePart F₂ H₂).card := by
  have hH₁ne : H₁.Nonempty :=
    Finset.card_pos.mp (by have := hH₁.2; omega)
  have hH₂ne : H₂.Nonempty :=
    Finset.card_pos.mp (by have := hH₂.2; omega)
  exact ⟨two_le_of_saturated_endpoints_homogeneous h₁ hend₁ hH₁,
    two_le_of_saturated_endpoints_homogeneous h₂ hend₂ hH₂,
    compose_saturated h₁ h₂ hend₁ hend₂ hH₁ hH₂,
    compose_hasEndpoints hend₁ hend₂,
    compose_homogeneousAtom hend₁ hend₂ hH₁ hH₂,
    compose_smallPart hH₁ne hH₂ne,
    compose_largePart hH₁ne hH₂ne,
    compose_card hH₁ne⟩

end AiMathLab.SaturatedSperner
