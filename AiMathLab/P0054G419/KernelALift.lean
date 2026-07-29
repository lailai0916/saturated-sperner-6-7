import AiMathLab.P0054G419.KernelACovers

namespace AiMathLab.P0054.G419

open G413
open scoped BigOperators

noncomputable def fourActualChoices {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) :
    Finset (Σ C : List FourSupportIndex, ∀ s ∈ C.toFinset, α) := by
  classical
  exact fourMinimalSupportIndexCovers.toFinset.sigma fun C ↦
    C.toFinset.pi fun s ↦ fourSupportFiber rowOrder s

noncomputable def fourChoiceRow {α : Type*} [DecidableEq α]
    (q : Σ C : List FourSupportIndex, ∀ s ∈ C.toFinset, α) : G413.Row α := by
  classical
  exact q.1.toFinset.attach.image fun s : q.1.toFinset ↦ q.2 s.1 s.2

theorem fourActualChoices_card {α : Type*} [DecidableEq α]
    {T : G413.Hypergraph α} (rowOrder : Fin 4 ≃ T) :
    (fourActualChoices rowOrder).card =
      fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) := by
  classical
  unfold fourActualChoices
  rw [Finset.card_sigma]
  rw [List.sum_toFinset _ four_minimal_support_index_covers_nodup]
  rw [← four_weighted_cover_count_eq_index_covers]
  apply congrArg List.sum
  apply List.map_congr_left
  intro C hC
  rw [Finset.card_pi]
  rw [List.prod_toFinset _
    (four_minimal_support_index_covers_each_sorted C
      hC).nodup]
  apply congrArg List.prod
  apply List.map_congr_left
  intro s _hs
  exact (fourMultiplicityDigit_actualSupportMultiplicity rowOrder s).symm

theorem exists_private_vertex_of_fourMinimalSupportCover
    {C : Finset FourSupportIndex} (hC : fourMinimalSupportCover C)
    {s : FourSupportIndex} (hsC : s ∈ C) :
    ∃ row ∈ fourSupport s,
      ∀ t ∈ C, row ∈ fourSupport t → t = s := by
  classical
  have hNotCover := hC.2 s hsC
  unfold fourSupportCovers at hNotCover
  push Not at hNotCover
  obtain ⟨row, hrow⟩ := hNotCover
  obtain ⟨t, htC, hrowt⟩ := hC.1 row
  have hts : t = s := by
    by_contra hne
    exact hrow t (Finset.mem_erase.mpr ⟨hne, htC⟩) hrowt
  subst t
  refine ⟨row, hrowt, ?_⟩
  intro t htC hrowt
  by_contra hne
  exact hrow t (Finset.mem_erase.mpr ⟨hne, htC⟩) hrowt

theorem fourChosenPoint_mem_choiceRow {α : Type*} [DecidableEq α]
    (C : List FourSupportIndex) (f : ∀ s ∈ C.toFinset, α)
    (s : FourSupportIndex) (hsC : s ∈ C.toFinset) :
    f s hsC ∈ fourChoiceRow ⟨C, f⟩ := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨⟨s, hsC⟩, Finset.mem_attach _ _, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Sigma membership and support-index normalization exceed the default budget.
theorem fourChoiceRow_supportIndices {α : Type*}
    [Fintype α] [DecidableEq α] {T : G413.Hypergraph α}
    (rowOrder : Fin 4 ≃ T)
    {q : Σ C : List FourSupportIndex, ∀ s ∈ C.toFinset, α}
    (hq : q ∈ fourActualChoices rowOrder) :
    (fourChoiceRow q).image (fourActualSupportIndex rowOrder) = q.1.toFinset := by
  classical
  obtain ⟨_hCover, hPi⟩ := Finset.mem_sigma.mp hq
  ext s
  constructor
  · intro hsImage
    obtain ⟨x, hxRow, hxIndex⟩ := Finset.mem_image.mp hsImage
    obtain ⟨t, _htAttach, htx⟩ := Finset.mem_image.mp hxRow
    have htC : t.1 ∈ q.1.toFinset := t.2
    have htFiber := Finset.mem_pi.mp hPi t.1 htC
    have htIndex : fourActualSupportIndex rowOrder (q.2 t.1 htC) = t.1 :=
      (Finset.mem_filter.mp htFiber).2
    have hst : s = t.1 := by
      calc
        s = fourActualSupportIndex rowOrder x := hxIndex.symm
        _ = fourActualSupportIndex rowOrder (q.2 t.1 htC) := by rw [htx]
        _ = t.1 := htIndex
    exact hst ▸ htC
  · intro hsC
    have hsFiber := Finset.mem_pi.mp hPi s hsC
    have hsIndex : fourActualSupportIndex rowOrder (q.2 s hsC) = s :=
      (Finset.mem_filter.mp hsFiber).2
    apply Finset.mem_image.mpr
    exact ⟨q.2 s hsC, fourChosenPoint_mem_choiceRow q.1 q.2 s hsC, hsIndex⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Recovering dependent choices from equal image rows needs extended elaboration.
theorem fourChoiceRow_injective {α : Type*}
    [Fintype α] [DecidableEq α] {T : G413.Hypergraph α}
    (rowOrder : Fin 4 ≃ T) :
    Set.InjOn fourChoiceRow (↑(fourActualChoices rowOrder) :
      Set (Σ C : List FourSupportIndex, ∀ s ∈ C.toFinset, α)) := by
  classical
  rintro ⟨C, f⟩ hq ⟨D, g⟩ hr hRows
  have hC := (Finset.mem_sigma.mp hq).1
  have hD := (Finset.mem_sigma.mp hr).1
  have hCDsets : C.toFinset = D.toFinset := by
    calc
      C.toFinset = (fourChoiceRow ⟨C, f⟩).image
          (fourActualSupportIndex rowOrder) :=
        (fourChoiceRow_supportIndices rowOrder hq).symm
      _ = (fourChoiceRow ⟨D, g⟩).image
          (fourActualSupportIndex rowOrder) := by rw [hRows]
      _ = D.toFinset := fourChoiceRow_supportIndices rowOrder hr
  have hCD : C = D :=
    four_minimal_support_index_covers_toFinset_injective hC hD hCDsets
  subst D
  have hfg : f = g := by
    funext s hsC
    have hfPi := (Finset.mem_sigma.mp hq).2
    have hgPi := (Finset.mem_sigma.mp hr).2
    have hfFiber := Finset.mem_pi.mp hfPi s hsC
    have hfIndex : fourActualSupportIndex rowOrder (f s hsC) = s :=
      (Finset.mem_filter.mp hfFiber).2
    have hfRow : f s hsC ∈ fourChoiceRow ⟨C, f⟩ :=
      fourChosenPoint_mem_choiceRow C f s hsC
    have hfRowG : f s hsC ∈ fourChoiceRow ⟨C, g⟩ := by
      rw [← hRows]
      exact hfRow
    obtain ⟨t, _htAttach, htg⟩ := Finset.mem_image.mp hfRowG
    have htC : t.1 ∈ C.toFinset := t.2
    have hgFiber := Finset.mem_pi.mp hgPi t.1 htC
    have hgIndex : fourActualSupportIndex rowOrder (g t.1 htC) = t.1 :=
      (Finset.mem_filter.mp hgFiber).2
    have hts : t.1 = s := by
      calc
        t.1 = fourActualSupportIndex rowOrder (g t.1 htC) := hgIndex.symm
        _ = fourActualSupportIndex rowOrder (f s hsC) := by
          simpa using congrArg (fourActualSupportIndex rowOrder) htg
        _ = s := hfIndex
    have ht : t = ⟨s, hsC⟩ := Subtype.ext hts
    subst t
    simpa using htg.symm
  exact congrArg (Sigma.mk C) hfg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The private-row minimal-transversal construction exceeds the default budget.
theorem fourChoiceRow_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α] {T : G413.Hypergraph α}
    (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2)
    {q : Σ C : List FourSupportIndex, ∀ s ∈ C.toFinset, α}
    (hq : q ∈ fourActualChoices rowOrder) :
    fourChoiceRow q ∈ blocker T := by
  classical
  obtain ⟨hCoverList, hPi⟩ := Finset.mem_sigma.mp hq
  have hCover : fourMinimalSupportCover q.1.toFinset :=
    four_minimal_support_index_covers_sound q.1
      (List.mem_toFinset.mp hCoverList)
  let hProper := fourRows_actual_support_proper rowOrder hBRows
  have hTransversal : IsTransversal T (fourChoiceRow q) := by
    intro E hET
    let e : T := ⟨E, hET⟩
    obtain ⟨row, hrow⟩ := rowOrder.surjective e
    obtain ⟨s, hsC, hrows⟩ := hCover.1 row
    have hsFiber := Finset.mem_pi.mp hPi s hsC
    obtain ⟨hsActive, hsIndex⟩ := Finset.mem_filter.mp hsFiber
    refine ⟨q.2 s hsC, fourChosenPoint_mem_choiceRow q.1 q.2 s hsC, ?_⟩
    have hSupport := fourSupport_actualSupportIndex rowOrder hProper hsActive
    have hrowSupport : row ∈ fourSupportOfPoint rowOrder (q.2 s hsC) := by
      rw [← hSupport, hsIndex]
      exact hrows
    have hxOrdered :=
      (mem_fourSupportOfPoint rowOrder (q.2 s hsC) row).mp hrowSupport
    have hRow : (rowOrder row : G413.Row α) = E := by
      simpa [e] using congrArg Subtype.val hrow
    simpa [hRow] using hxOrdered
  apply mem_blocker.mpr
  apply hTransversal.minimal_of_privateRows
  intro x hxRow
  obtain ⟨s, _hsAttach, hsx⟩ := Finset.mem_image.mp hxRow
  have hsC : s.1 ∈ q.1.toFinset := s.2
  have hsFiber := Finset.mem_pi.mp hPi s.1 hsC
  obtain ⟨hsActive, hsIndex⟩ := Finset.mem_filter.mp hsFiber
  obtain ⟨row, hrows, hrowPrivate⟩ :=
    exists_private_vertex_of_fourMinimalSupportCover hCover hsC
  let E : G413.Row α := rowOrder row
  refine ⟨E, (rowOrder row).property, hxRow, ?_, ?_⟩
  · rw [← hsx]
    apply (mem_fourSupportOfPoint rowOrder (q.2 s.1 hsC) row).mp
    have hSupport := fourSupport_actualSupportIndex rowOrder hProper hsActive
    rw [← hSupport, hsIndex]
    exact hrows
  · intro y hyRow hyE
    obtain ⟨t, _htAttach, hty⟩ := Finset.mem_image.mp hyRow
    have htC : t.1 ∈ q.1.toFinset := t.2
    have htFiber := Finset.mem_pi.mp hPi t.1 htC
    obtain ⟨htActive, htIndex⟩ := Finset.mem_filter.mp htFiber
    have hrowSupportPoint :
        row ∈ fourSupportOfPoint rowOrder (q.2 t.1 htC) := by
      apply (mem_fourSupportOfPoint rowOrder (q.2 t.1 htC) row).mpr
      simpa [E] using hty ▸ hyE
    have hSupport := fourSupport_actualSupportIndex rowOrder hProper htActive
    have hrowt : row ∈ fourSupport t.1 := by
      rw [← htIndex, hSupport]
      exact hrowSupportPoint
    have hts : t.1 = s.1 := hrowPrivate t.1 htC hrowt
    have ht : t = s := Subtype.ext hts
    subst t
    simpa using hty.symm.trans hsx

theorem fourWeightedCoverCount_le_blocker_card {α : Type*}
    [Fintype α] [DecidableEq α] {T : G413.Hypergraph α}
    (rowOrder : Fin 4 ≃ T)
    (hBRows : RowsCardAtLeast (blocker T) 2) :
    fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) ≤
      (blocker T).card := by
  classical
  have hImageSubset :
      (fourActualChoices rowOrder).image fourChoiceRow ⊆ blocker T := by
    intro B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    exact fourChoiceRow_mem_blocker rowOrder hBRows hq
  calc
    fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) =
        (fourActualChoices rowOrder).card :=
      (fourActualChoices_card rowOrder).symm
    _ = ((fourActualChoices rowOrder).image fourChoiceRow).card :=
      (Finset.card_image_iff.mpr (fourChoiceRow_injective rowOrder)).symm
    _ ≤ (blocker T).card := Finset.card_le_card hImageSubset

end AiMathLab.P0054.G419
