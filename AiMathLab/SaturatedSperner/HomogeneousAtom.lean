import AiMathLab.SaturatedSperner.Equiv

/-!
# Homogeneous atoms in finite set families

The definitions in this file follow the source convention: a homogeneous
atom is a maximal all-or-none block containing more than two points.  The
transport theorems move the full maximality quantifier through an equivalence;
they do not merely transport the members of the family.
-/

universe u v

namespace AiMathLab.SaturatedSperner

variable {α : Type u} {β : Type v}
  [DecidableEq α] [DecidableEq β]

/-- Every family member contains all of `H` or is disjoint from `H`. -/
def IsAtomBlock (F : Family α) (H : Finset α) : Prop :=
  ∀ S, S ∈ F → Disjoint S H ∨ H ⊆ S

/-- An atom is a maximal all-or-none block. -/
def IsAtom (F : Family α) (H : Finset α) : Prop :=
  IsAtomBlock F H ∧
    ∀ K, H ⊂ K → ¬ IsAtomBlock F K

/-- A homogeneous atom is an atom of cardinality strictly greater than two. -/
def IsHomogeneousAtom (F : Family α) (H : Finset α) : Prop :=
  IsAtom F H ∧ 2 < H.card

@[simp] theorem mapSubset_subset_iff
    (e : α ≃ β) (A B : Finset α) :
    mapSubset e A ⊆ mapSubset e B ↔ A ⊆ B := by
  simp [mapSubset, Equiv.finsetCongr_apply, Finset.map_subset_map]

@[simp] theorem mapSubset_disjoint_iff
    (e : α ≃ β) (A B : Finset α) :
    Disjoint (mapSubset e A) (mapSubset e B) ↔ Disjoint A B := by
  simp [mapSubset, Equiv.finsetCongr_apply, Finset.disjoint_map]

@[simp] theorem mapSubset_card
    (e : α ≃ β) (A : Finset α) :
    (mapSubset e A).card = A.card := by
  simp [mapSubset, Equiv.finsetCongr_apply]

private theorem isAtomBlock_mapFamily_forward
    (e : α ≃ β) {F : Family α} {H : Finset α}
    (h : IsAtomBlock F H) :
    IsAtomBlock (mapFamily e F) (mapSubset e H) := by
  intro T hTF
  let S := mapSubset e.symm T
  have hST : mapSubset e S = T := by simp [S]
  have hSF : S ∈ F := by
    exact (mem_mapFamily_symm_iff e T F).mp hTF
  rcases h S hSF with hdisj | hsub
  · left
    simpa [hST] using (mapSubset_disjoint_iff e S H).mpr hdisj
  · right
    simpa [hST] using (mapSubset_subset_iff e H S).mpr hsub

/-- All-or-none blockness is invariant under a ground-type equivalence. -/
theorem isAtomBlock_mapFamily_iff
    (e : α ≃ β) (F : Family α) (H : Finset α) :
    IsAtomBlock (mapFamily e F) (mapSubset e H) ↔
      IsAtomBlock F H := by
  constructor
  · intro h
    have hm := isAtomBlock_mapFamily_forward e.symm h
    simpa using hm
  · exact isAtomBlock_mapFamily_forward e

private theorem isAtom_mapFamily_forward
    (e : α ≃ β) {F : Family α} {H : Finset α}
    (h : IsAtom F H) :
    IsAtom (mapFamily e F) (mapSubset e H) := by
  refine ⟨(isAtomBlock_mapFamily_iff e F H).mpr h.1, ?_⟩
  intro K hHK hKblock
  let L := mapSubset e.symm K
  have hHL : H ⊂ L := by
    apply (mapSubset_ssubset_iff e H L).mp
    simpa [L] using hHK
  have htransported :
      IsAtomBlock (mapFamily e F) (mapSubset e L) :=
    by simpa [L] using hKblock
  exact h.2 L hHL ((isAtomBlock_mapFamily_iff e F L).mp htransported)

/-- Atom maximality, including arbitrary strict extensions, is invariant
under a ground-type equivalence. -/
theorem isAtom_mapFamily_iff
    (e : α ≃ β) (F : Family α) (H : Finset α) :
    IsAtom (mapFamily e F) (mapSubset e H) ↔ IsAtom F H := by
  constructor
  · intro h
    have hm := isAtom_mapFamily_forward e.symm h
    simpa using hm
  · exact isAtom_mapFamily_forward e

/-- Homogeneous atoms are invariant under a ground-type equivalence. -/
theorem isHomogeneousAtom_mapFamily_iff
    (e : α ≃ β) (F : Family α) (H : Finset α) :
    IsHomogeneousAtom (mapFamily e F) (mapSubset e H) ↔
      IsHomogeneousAtom F H := by
  simp only [IsHomogeneousAtom, isAtom_mapFamily_iff, mapSubset_card]

end AiMathLab.SaturatedSperner
