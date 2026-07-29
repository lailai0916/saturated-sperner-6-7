import AiMathLab.SaturatedSperner.HomogeneousAtom

/-!
# A finite incidence pigeonhole theorem for homogeneous atoms

Points are grouped by their membership signatures across a finite family.
If the ground type has at least three times as many points as signatures,
one signature class has at least three points.  That class is a maximal
all-or-none block, hence a homogeneous atom.
-/

universe u

namespace AiMathLab.SaturatedSperner

variable {α : Type u} [Fintype α] [DecidableEq α]

abbrev IncidenceCode (F : Family α) := ↑F.powerset

def incidenceCode (F : Family α) (x : α) : IncidenceCode F :=
  ⟨F.filter fun S => x ∈ S, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩

@[simp] theorem card_incidenceCode (F : Family α) :
    Fintype.card (IncidenceCode F) = 2 ^ F.card := by
  rw [Fintype.card_coe, Finset.card_powerset]

def incidenceFiber (F : Family α) (q : IncidenceCode F) : Finset α :=
  Finset.univ.filter fun x => incidenceCode F x = q

@[simp] theorem mem_incidenceFiber_iff
    (F : Family α) (q : IncidenceCode F) (x : α) :
    x ∈ incidenceFiber F q ↔ incidenceCode F x = q := by
  simp [incidenceFiber]

theorem incidenceFiber_atomBlock
    {F : Family α} {q : IncidenceCode F}
    (hq : (incidenceFiber F q).Nonempty) :
    IsAtomBlock F (incidenceFiber F q) := by
  rcases hq with ⟨a, haH⟩
  have haCode : incidenceCode F a = q :=
    (mem_incidenceFiber_iff F q a).mp haH
  intro S hSF
  have hsame (x : α) (hxH : x ∈ incidenceFiber F q) :
      (x ∈ S ↔ a ∈ S) := by
    have hxCode : incidenceCode F x = q :=
      (mem_incidenceFiber_iff F q x).mp hxH
    have hval := congrArg Subtype.val (hxCode.trans haCode.symm)
    have hmem := Finset.ext_iff.mp hval S
    simpa [incidenceCode, hSF] using hmem
  by_cases haS : a ∈ S
  · right
    intro x hxH
    exact (hsame x hxH).mpr haS
  · left
    rw [Finset.disjoint_left]
    intro x hxS hxH
    exact haS ((hsame x hxH).mp hxS)

theorem incidenceFiber_atom_maximal
    {F : Family α} {q : IncidenceCode F}
    (hq : (incidenceFiber F q).Nonempty) :
    ∀ K, incidenceFiber F q ⊂ K → ¬ IsAtomBlock F K := by
  rcases hq with ⟨a, haH⟩
  have haCode : incidenceCode F a = q :=
    (mem_incidenceFiber_iff F q a).mp haH
  intro K hHK hblock
  rcases Finset.exists_of_ssubset hHK with ⟨z, hzK, hznotH⟩
  have hzCode : incidenceCode F z ≠ incidenceCode F a := by
    intro hza
    apply hznotH
    apply (mem_incidenceFiber_iff F q z).mpr
    exact hza.trans haCode
  have hmismatch : ∃ S, S ∈ F ∧
      ((z ∈ S ∧ a ∉ S) ∨ (z ∉ S ∧ a ∈ S)) := by
    by_contra hnone
    have hall : ∀ S, S ∈ F → (z ∈ S ↔ a ∈ S) := by
      intro S hSF
      by_cases hzS : z ∈ S
      · constructor
        · intro _
          by_contra haS
          exact hnone ⟨S, hSF, Or.inl ⟨hzS, haS⟩⟩
        · intro _
          exact hzS
      · constructor
        · intro h
          exact False.elim (hzS h)
        · intro haS
          exact False.elim (hnone ⟨S, hSF, Or.inr ⟨hzS, haS⟩⟩)
    apply hzCode
    apply Subtype.ext
    ext S
    by_cases hSF : S ∈ F
    · simpa [incidenceCode, hSF] using hall S hSF
    · simp [incidenceCode, hSF]
  rcases hmismatch with ⟨S, hSF, hza | haz⟩
  · rcases hblock S hSF with hdisj | hsub
    · exact Finset.disjoint_left.mp hdisj hza.1 hzK
    · exact hza.2 (hsub (hHK.le haH))
  · rcases hblock S hSF with hdisj | hsub
    · exact Finset.disjoint_left.mp hdisj haz.2 (hHK.le haH)
    · exact haz.1 (hsub hzK)

theorem exists_homogeneousAtom_of_signature_bound
    (F : Family α)
    (hground : 3 * 2 ^ F.card ≤ Fintype.card α) :
    ∃ H : Finset α, IsHomogeneousAtom F H := by
  let f : α → IncidenceCode F := incidenceCode F
  letI : Nonempty (IncidenceCode F) :=
    ⟨⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩⟩
  have hmul : Fintype.card (IncidenceCode F) * 3 ≤ Fintype.card α := by
    rw [card_incidenceCode]
    simpa [Nat.mul_comm] using hground
  rcases Fintype.exists_le_card_fiber_of_mul_le_card (f := f) hmul with
    ⟨q, hq⟩
  let H := incidenceFiber F q
  have hcard : 3 ≤ H.card := by
    simpa [H, incidenceFiber, f] using hq
  have hne : H.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨H, ⟨⟨?_, ?_⟩, by omega⟩⟩
  · exact incidenceFiber_atomBlock hne
  · exact incidenceFiber_atom_maximal hne

end AiMathLab.SaturatedSperner
