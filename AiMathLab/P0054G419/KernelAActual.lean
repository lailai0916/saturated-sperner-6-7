import AiMathLab.P0054G419.KernelAClassificationSound
import AiMathLab.P0054G419.KernelProfile

namespace AiMathLab.P0054.G419

open G413

abbrev FourVertex := Fin 4
abbrev FourSupportIndex := Fin 14

def fourSupport (s : FourSupportIndex) : Finset FourVertex :=
  Finset.univ.filter fun row ↦ fourSupportContains s.val row.val

theorem mem_fourSupport (s : FourSupportIndex) (row : FourVertex) :
    row ∈ fourSupport s ↔ fourSupportContains s.val row.val = true := by
  simp [fourSupport]

theorem fourSupport_injective : Function.Injective fourSupport := by
  decide

set_option maxRecDepth 100000 in
theorem fourSupport_complete :
    ∀ S : Finset FourVertex, S.Nonempty → S.card < 4 →
      ∃ s : FourSupportIndex, fourSupport s = S := by
  decide

theorem fourSupport_existsUnique
    (S : Finset FourVertex) (hS : S.Nonempty) (hProper : S.card < 4) :
    ∃! s : FourSupportIndex, fourSupport s = S := by
  obtain ⟨s, hs⟩ := fourSupport_complete S hS hProper
  exact ⟨s, hs, fun t ht ↦ fourSupport_injective (ht.trans hs.symm)⟩

noncomputable def fourSupportIndexOf (S : Finset FourVertex) : FourSupportIndex :=
  if h : S.Nonempty ∧ S.card < 4 then
    (fourSupport_existsUnique S h.1 h.2).choose
  else 0

theorem fourSupport_indexOf {S : Finset FourVertex}
    (hS : S.Nonempty) (hProper : S.card < 4) :
    fourSupport (fourSupportIndexOf S) = S := by
  rw [fourSupportIndexOf, dif_pos ⟨hS, hProper⟩]
  exact (fourSupport_existsUnique S hS hProper).choose_spec.1

def fourActiveUniverse {α : Type*} [DecidableEq α]
    (T : G413.Hypergraph α) : Finset α :=
  T.biUnion fun E ↦ E

theorem mem_fourActiveUniverse {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} {x : α} :
    x ∈ fourActiveUniverse T ↔ ∃ E ∈ T, x ∈ E := by
  simp [fourActiveUniverse]

noncomputable def fourRowOrder {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (hTCard : T.card = 4) : Fin 4 ≃ T := by
  classical
  exact (Fintype.equivFinOfCardEq (by simpa using hTCard)).symm

def fourSupportOfPoint {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) (x : α) : Finset FourVertex :=
  Finset.univ.filter fun row ↦ x ∈ (rowOrder row : Row α)

theorem mem_fourSupportOfPoint {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) (x : α) (row : FourVertex) :
    row ∈ fourSupportOfPoint rowOrder x ↔ x ∈ (rowOrder row : Row α) := by
  simp [fourSupportOfPoint]

theorem fourSupportOfPoint_nonempty {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) {x : α}
    (hx : x ∈ fourActiveUniverse T) :
    (fourSupportOfPoint rowOrder x).Nonempty := by
  obtain ⟨E, hET, hxE⟩ := mem_fourActiveUniverse.mp hx
  let e : T := ⟨E, hET⟩
  obtain ⟨row, hrow⟩ := rowOrder.surjective e
  refine ⟨row, (mem_fourSupportOfPoint rowOrder x row).mpr ?_⟩
  simpa [e, hrow] using hxE

theorem fourSupportOfPoint_card_lt_four {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) (x : α)
    (hMissing : ∃ row : FourVertex, x ∉ (rowOrder row : Row α)) :
    (fourSupportOfPoint rowOrder x).card < 4 := by
  obtain ⟨row, hrow⟩ := hMissing
  have hProper : fourSupportOfPoint rowOrder x ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro hEq
    have : row ∈ fourSupportOfPoint rowOrder x := by rw [hEq]; simp
    exact hrow ((mem_fourSupportOfPoint rowOrder x row).mp this)
  have hCard := Finset.card_lt_card hProper
  simpa using hCard

noncomputable def fourActualSupportIndex {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) (x : α) : FourSupportIndex :=
  fourSupportIndexOf (fourSupportOfPoint rowOrder x)

noncomputable def fourSupportFiber {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) (s : FourSupportIndex) : Finset α :=
  (fourActiveUniverse T).filter fun x ↦ fourActualSupportIndex rowOrder x = s

noncomputable def fourActualSupportMultiplicity {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) : FourMultiplicity :=
  Array.ofFn fun s : FourSupportIndex ↦ (fourSupportFiber rowOrder s).card

theorem fourMultiplicityDigit_actualSupportMultiplicity {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) (s : FourSupportIndex) :
    fourMultiplicityDigit (fourActualSupportMultiplicity rowOrder) s.val =
      (fourSupportFiber rowOrder s).card := by
  simp [fourMultiplicityDigit, fourActualSupportMultiplicity]

theorem fourSupport_actualSupportIndex {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T)
    (hProper : ∀ x ∈ fourActiveUniverse T,
      ∃ row : FourVertex, x ∉ (rowOrder row : Row α))
    {x : α} (hx : x ∈ fourActiveUniverse T) :
    fourSupport (fourActualSupportIndex rowOrder x) = fourSupportOfPoint rowOrder x := by
  apply fourSupport_indexOf
  · exact fourSupportOfPoint_nonempty rowOrder hx
  · exact fourSupportOfPoint_card_lt_four rowOrder x (hProper x hx)

end AiMathLab.P0054.G419
