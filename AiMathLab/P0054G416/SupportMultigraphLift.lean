import AiMathLab.P0054G416.SupportMultigraphActual

namespace AiMathLab.P0054.G416

open G413
open scoped BigOperators

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed 111-entry certificate is checked by kernel reduction.
theorem five_minimal_support_covers_nodup : fiveMinimalSupportCovers.Nodup := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed 111-entry certificate is checked by kernel reduction.
theorem five_minimal_support_covers_each_nodup :
    ∀ C ∈ fiveMinimalSupportCovers, C.Nodup := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Pairwise comparison of the fixed cover certificate needs an unbounded heartbeat budget.
theorem five_minimal_support_covers_toFinset_injective :
    Set.InjOn List.toFinset (↑fiveMinimalSupportCovers.toFinset : Set (List FiveSupportIndex)) := by
  decide

noncomputable def fiveActualChoices {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 5 ≃ H) :
    Finset (Σ C : List FiveSupportIndex, ∀ s ∈ C.toFinset, α) := by
  classical
  exact fiveMinimalSupportCovers.toFinset.sigma fun C ↦
    C.toFinset.pi fun s ↦ supportFiber J rowOrder s

noncomputable def fiveChoiceRow {α : Type*} [DecidableEq α]
    (q : Σ C : List FiveSupportIndex, ∀ s ∈ C.toFinset, α) : G413.Row α := by
  classical
  exact q.1.toFinset.attach.image fun s : q.1.toFinset ↦ q.2 s.1 s.2

theorem fiveActualChoices_card {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 5 ≃ H) :
    (fiveActualChoices J rowOrder).card =
      fiveWeightedCoverCount (actualSupportMultiplicity J rowOrder) := by
  classical
  unfold fiveActualChoices fiveWeightedCoverCount
  rw [Finset.card_sigma]
  rw [← List.sum_toFinset _ five_minimal_support_covers_nodup]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.card_pi]
  rw [List.prod_toFinset _
    (five_minimal_support_covers_each_nodup C (List.mem_toFinset.mp hC))]
  have hCoerce : (do let s ← C; pure (s : Nat)) = C.map fun s ↦ s.val := by
    simpa [Function.comp_def] using
      (List.flatMap_pure_eq_map (fun s : FiveSupportIndex ↦ s.val) C)
  rw [hCoerce, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s hs
  exact (fiveMultiplicityDigit_actualSupportMultiplicity J rowOrder s).symm

theorem exists_private_vertex_of_fiveMinimalSupportCover
    {C : Finset FiveSupportIndex} (hC : fiveMinimalSupportCover C)
    {s : FiveSupportIndex} (hsC : s ∈ C) :
    ∃ v ∈ fiveSupport s,
      ∀ t ∈ C, v ∈ fiveSupport t → t = s := by
  classical
  have hNotCover := hC.2 s hsC
  unfold fiveSupportCovers at hNotCover
  push Not at hNotCover
  obtain ⟨v, hv⟩ := hNotCover
  obtain ⟨t, htC, hvt⟩ := hC.1 v
  have hts : t = s := by
    by_contra hne
    exact hv t (Finset.mem_erase.mpr ⟨hne, htC⟩) hvt
  subst t
  refine ⟨v, hvt, ?_⟩
  intro t htC hvt
  by_contra hne
  exact hv t (Finset.mem_erase.mpr ⟨hne, htC⟩) hvt

theorem fiveChosenPoint_mem_choiceRow {α : Type*} [DecidableEq α]
    (C : List FiveSupportIndex) (f : ∀ s ∈ C.toFinset, α)
    (s : FiveSupportIndex) (hsC : s ∈ C.toFinset) :
    f s hsC ∈ fiveChoiceRow ⟨C, f⟩ := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨⟨s, hsC⟩, Finset.mem_attach _ _, rfl⟩

set_option maxRecDepth 100000 in
theorem fiveChoiceRow_supportIndices {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 5 ≃ H)
    {q : Σ C : List FiveSupportIndex, ∀ s ∈ C.toFinset, α}
    (hq : q ∈ fiveActualChoices J rowOrder) :
    (fiveChoiceRow q).image (actualSupportIndex rowOrder) = q.1.toFinset := by
  classical
  obtain ⟨_hCover, hPi⟩ := Finset.mem_sigma.mp hq
  ext s
  constructor
  · intro hsImage
    obtain ⟨x, hxRow, hxIndex⟩ := Finset.mem_image.mp hsImage
    obtain ⟨t, htAttach, htx⟩ := Finset.mem_image.mp hxRow
    have htC : t.1 ∈ q.1.toFinset := t.2
    have htFiber := Finset.mem_pi.mp hPi t.1 htC
    have htIndex : actualSupportIndex rowOrder (q.2 t.1 htC) = t.1 :=
      (Finset.mem_filter.mp htFiber).2
    have hst : s = t.1 := by
      calc
        s = actualSupportIndex rowOrder x := hxIndex.symm
        _ = actualSupportIndex rowOrder (q.2 t.1 htC) := by rw [htx]
        _ = t.1 := htIndex
    exact hst ▸ htC
  · intro hsC
    have hsFiber := Finset.mem_pi.mp hPi s hsC
    have hsIndex : actualSupportIndex rowOrder (q.2 s hsC) = s :=
      (Finset.mem_filter.mp hsFiber).2
    apply Finset.mem_image.mpr
    refine ⟨q.2 s hsC, fiveChosenPoint_mem_choiceRow q.1 q.2 s hsC, hsIndex⟩

set_option maxRecDepth 100000 in
theorem fiveChoiceRow_injective {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 5 ≃ H) :
    Set.InjOn fiveChoiceRow (↑(fiveActualChoices J rowOrder) :
      Set (Σ C : List FiveSupportIndex, ∀ s ∈ C.toFinset, α)) := by
  classical
  rintro ⟨C, f⟩ hq ⟨D, g⟩ hr hRows
  have hC := (Finset.mem_sigma.mp hq).1
  have hD := (Finset.mem_sigma.mp hr).1
  have hCDsets : C.toFinset = D.toFinset := by
    calc
      C.toFinset = (fiveChoiceRow ⟨C, f⟩).image (actualSupportIndex rowOrder) :=
        (fiveChoiceRow_supportIndices rowOrder hq).symm
      _ = (fiveChoiceRow ⟨D, g⟩).image (actualSupportIndex rowOrder) := by rw [hRows]
      _ = D.toFinset := fiveChoiceRow_supportIndices rowOrder hr
  have hCD : C = D :=
    five_minimal_support_covers_toFinset_injective hC hD hCDsets
  subst D
  have hfg : f = g := by
    funext s hsC
    have hfPi := (Finset.mem_sigma.mp hq).2
    have hgPi := (Finset.mem_sigma.mp hr).2
    have hfFiber := Finset.mem_pi.mp hfPi s hsC
    have hfIndex : actualSupportIndex rowOrder (f s hsC) = s :=
      (Finset.mem_filter.mp hfFiber).2
    have hfRow : f s hsC ∈ fiveChoiceRow ⟨C, f⟩ :=
      fiveChosenPoint_mem_choiceRow C f s hsC
    have hfRowG : f s hsC ∈ fiveChoiceRow ⟨C, g⟩ := by
      rw [← hRows]
      exact hfRow
    obtain ⟨t, htAttach, htg⟩ := Finset.mem_image.mp hfRowG
    have htC : t.1 ∈ C.toFinset := t.2
    have hgFiber := Finset.mem_pi.mp hgPi t.1 htC
    have hgIndex : actualSupportIndex rowOrder (g t.1 htC) = t.1 :=
      (Finset.mem_filter.mp hgFiber).2
    have hts : t.1 = s := by
      calc
        t.1 = actualSupportIndex rowOrder (g t.1 htC) := hgIndex.symm
        _ = actualSupportIndex rowOrder (f s hsC) := by
          simpa using congrArg (actualSupportIndex rowOrder) htg
        _ = s := hfIndex
    have ht : t = ⟨s, hsC⟩ := Subtype.ext hts
    subst t
    simpa using htg.symm
  exact congrArg (Sigma.mk C) hfg

set_option maxRecDepth 100000 in
theorem fiveChoiceRow_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 5 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2)
    {q : Σ C : List FiveSupportIndex, ∀ s ∈ C.toFinset, α}
    (hq : q ∈ fiveActualChoices J rowOrder) :
    fiveChoiceRow q ∈ blocker H := by
  classical
  obtain ⟨hCoverList, hPi⟩ := Finset.mem_sigma.mp hq
  have hCover : fiveMinimalSupportCover q.1.toFinset :=
    five_minimal_support_covers_sound (List.mem_toFinset.mp hCoverList)
  have hTransversal : IsTransversal H (fiveChoiceRow q) := by
    intro E hEH
    let e : H := ⟨E, hEH⟩
    obtain ⟨v, hv⟩ := rowOrder.surjective e
    obtain ⟨s, hsC, hvs⟩ := hCover.1 v
    have hsFiber := Finset.mem_pi.mp hPi s hsC
    obtain ⟨hsJ, hsIndex⟩ := Finset.mem_filter.mp hsFiber
    refine ⟨q.2 s hsC, fiveChosenPoint_mem_choiceRow q.1 q.2 s hsC, ?_⟩
    have hSupport :=
      fiveSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hsJ
    have hvSupport : v ∈ supportOfPoint rowOrder (q.2 s hsC) := by
      rw [← hSupport, hsIndex]
      exact hvs
    have hxOrdered := (mem_supportOfPoint rowOrder (q.2 s hsC) v).mp hvSupport
    have hRow : (rowOrder v : G413.Row α) = E := by
      simpa [e] using congrArg Subtype.val hv
    simpa [hRow] using hxOrdered
  apply mem_blocker.mpr
  apply hTransversal.minimal_of_privateRows
  intro x hxRow
  obtain ⟨s, hsAttach, hsx⟩ := Finset.mem_image.mp hxRow
  have hsC : s.1 ∈ q.1.toFinset := s.2
  have hsFiber := Finset.mem_pi.mp hPi s.1 hsC
  obtain ⟨hsJ, hsIndex⟩ := Finset.mem_filter.mp hsFiber
  obtain ⟨v, hvs, hvPrivate⟩ :=
    exists_private_vertex_of_fiveMinimalSupportCover hCover hsC
  let E : G413.Row α := rowOrder v
  refine ⟨E, (rowOrder v).property, hxRow, ?_, ?_⟩
  · rw [← hsx]
    apply (mem_supportOfPoint rowOrder (q.2 s.1 hsC) v).mp
    have hSupport :=
      fiveSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hsJ
    rw [← hSupport, hsIndex]
    exact hvs
  · intro y hyRow hyE
    obtain ⟨t, htAttach, hty⟩ := Finset.mem_image.mp hyRow
    have htC : t.1 ∈ q.1.toFinset := t.2
    have htFiber := Finset.mem_pi.mp hPi t.1 htC
    obtain ⟨htJ, htIndex⟩ := Finset.mem_filter.mp htFiber
    have hvtSupportPoint : v ∈ supportOfPoint rowOrder (q.2 t.1 htC) := by
      apply (mem_supportOfPoint rowOrder (q.2 t.1 htC) v).mpr
      simpa [E] using hty ▸ hyE
    have hSupport :=
      fiveSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree htJ
    have hvt : v ∈ fiveSupport t.1 := by
      rw [← htIndex, hSupport]
      exact hvtSupportPoint
    have hts : t.1 = s.1 := hvPrivate t.1 htC hvt
    have ht : t = s := Subtype.ext hts
    subst t
    simpa using hty.symm.trans hsx

set_option maxRecDepth 100000 in
theorem fiveRow_lowDegree_blocker_card_ge_fifteen {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α}
    (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hMaxDegree : MaxDegreeAtMost H 2) :
    15 ≤ (blocker H).card := by
  classical
  obtain ⟨J, hCore, hMinimal⟩ := exists_minimal_three_core hHRows
  let rowOrder := coreRowOrder hHcard J
  have hLow : 3 ≤ (lowCoreRows H J).card :=
    lowCoreRows_card_ge_three hHcard hCore hMinimal hMaxDegree
  have hHigh : (lowCoreRows H J).card ≤ 5 :=
    lowCoreRows_card_le_five hHcard J
  have hValid : FiveMultiplicityValid (lowCoreRows H J).card
      (actualSupportMultiplicity J rowOrder) := by
    simpa [rowOrder] using
      actualSupportMultiplicity_valid hHcard hCore hMinimal hMaxDegree
  have hWeighted :
      15 ≤ fiveWeightedCoverCount (actualSupportMultiplicity J rowOrder) := by
    have hCertificate := five_support_multigraph_weighted_cover_count_ge_fifteen
      (lowCoreRows H J).card
      (supportFiber J rowOrder 0).card
      (supportFiber J rowOrder 1).card
      (supportFiber J rowOrder 2).card
      (supportFiber J rowOrder 3).card
      (supportFiber J rowOrder 4).card
      (supportFiber J rowOrder 5).card
      (supportFiber J rowOrder 6).card
      (supportFiber J rowOrder 7).card
      (supportFiber J rowOrder 8).card
      (supportFiber J rowOrder 9).card
      (supportFiber J rowOrder 10).card
      (supportFiber J rowOrder 11).card
      (supportFiber J rowOrder 12).card
      (supportFiber J rowOrder 13).card
      (supportFiber J rowOrder 14).card
      hLow hHigh (by simpa [actualSupportMultiplicity] using hValid)
    simpa [actualSupportMultiplicity] using hCertificate
  have hImageSubset :
      (fiveActualChoices J rowOrder).image fiveChoiceRow ⊆ blocker H := by
    intro T hT
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
    exact fiveChoiceRow_mem_blocker rowOrder hCore hMinimal hMaxDegree hq
  calc
    15 ≤ fiveWeightedCoverCount (actualSupportMultiplicity J rowOrder) := hWeighted
    _ = (fiveActualChoices J rowOrder).card := (fiveActualChoices_card J rowOrder).symm
    _ = ((fiveActualChoices J rowOrder).image fiveChoiceRow).card :=
      (Finset.card_image_iff.mpr (fiveChoiceRow_injective rowOrder)).symm
    _ ≤ (blocker H).card := Finset.card_le_card hImageSubset

theorem fiveEleven_lowDegree_impossible {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α}
    (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBcard : (blocker H).card = 11)
    (hMaxDegree : MaxDegreeAtMost H 2) : False := by
  have hLower :=
    fiveRow_lowDegree_blocker_card_ge_fifteen hHcard hHRows hMaxDegree
  omega

theorem fiveEleven_impossible {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α}
    (hHclutter : IsClutter H)
    (hHcard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBcard : (blocker H).card = 11) : False := by
  have hDegreeUpper := fiveRow_maxDegreeAtMost_three hHcard hHRows hBRows
  by_cases hLowDegree : MaxDegreeAtMost H 2
  · exact fiveEleven_lowDegree_impossible hHcard hHRows hBcard hLowDegree
  · unfold MaxDegreeAtMost at hLowDegree
    push Not at hLowDegree
    obtain ⟨x, hxDegree⟩ := hLowDegree
    have hDegreeThree : degree H x = 3 := by
      have hUpper := hDegreeUpper x
      omega
    exact G415.fiveEleven_degreeThree_impossible hHclutter hHcard hHRows hBRows hBcard
      hDegreeThree

end AiMathLab.P0054.G416
