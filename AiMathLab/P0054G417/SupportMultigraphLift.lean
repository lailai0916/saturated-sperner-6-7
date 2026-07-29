import AiMathLab.P0054G417.SupportMultigraphActual
import AiMathLab.P0054G417.SupportMultigraphCertificate

namespace AiMathLab.P0054.G417

open G413
open G416
open scoped BigOperators

-- Dependent theorem types make this naming linter exceed its heartbeat budget.
set_option linter.constructorNameAsVariable false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The exhaustive cover list requires kernel evaluation beyond the default budget.
theorem six_minimal_support_covers_nodup : sixMinimalSupportCovers.Nodup := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The exhaustive cover list requires kernel evaluation beyond the default budget.
theorem six_minimal_support_covers_each_sorted :
    ∀ C ∈ sixMinimalSupportCovers, C.Pairwise (· < ·) := by
  decide

theorem six_minimal_support_covers_toFinset_injective :
    Set.InjOn List.toFinset (↑sixMinimalSupportCovers.toFinset : Set (List SixSupportIndex)) := by
  intro C hC D hD hSets
  have hCSorted :=
    six_minimal_support_covers_each_sorted C (List.mem_toFinset.mp hC)
  have hDSorted :=
    six_minimal_support_covers_each_sorted D (List.mem_toFinset.mp hD)
  have hPerm := List.perm_of_nodup_nodup_toFinset_eq hCSorted.nodup hDSorted.nodup hSets
  exact hPerm.eq_of_pairwise' hCSorted hDSorted

noncomputable def sixActualChoices {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 6 ≃ H) :
    Finset (Σ C : List SixSupportIndex, ∀ s ∈ C.toFinset, α) := by
  classical
  exact sixMinimalSupportCovers.toFinset.sigma fun C ↦
    C.toFinset.pi fun s ↦ sixSupportFiber J rowOrder s

noncomputable def sixChoiceRow {α : Type*} [DecidableEq α]
    (q : Σ C : List SixSupportIndex, ∀ s ∈ C.toFinset, α) : G413.Row α := by
  classical
  exact q.1.toFinset.attach.image fun s : q.1.toFinset ↦ q.2 s.1 s.2

theorem sixActualChoices_card {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 6 ≃ H) :
    (sixActualChoices J rowOrder).card =
      sixWeightedCoverCount (sixActualSupportMultiplicity J rowOrder) := by
  classical
  unfold sixActualChoices sixWeightedCoverCount
  rw [Finset.card_sigma]
  rw [← List.sum_toFinset _ six_minimal_support_covers_nodup]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.card_pi]
  rw [List.prod_toFinset _
    (six_minimal_support_covers_each_sorted C (List.mem_toFinset.mp hC)).nodup]
  have hCoerce : (do let s ← C; pure (s : Nat)) = C.map fun s ↦ s.val := by
    simpa [Function.comp_def] using
      (List.flatMap_pure_eq_map (fun s : SixSupportIndex ↦ s.val) C)
  rw [hCoerce, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s hs
  exact (sixMultiplicityDigit_actualSupportMultiplicity J rowOrder s).symm

theorem exists_private_vertex_of_sixMinimalSupportCover
    {C : Finset SixSupportIndex} (hC : sixMinimalSupportCover C)
    {s : SixSupportIndex} (hsC : s ∈ C) :
    ∃ v ∈ sixSupport s,
      ∀ t ∈ C, v ∈ sixSupport t → t = s := by
  classical
  have hNotCover := hC.2 s hsC
  unfold sixSupportCovers at hNotCover
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

theorem sixChosenPoint_mem_choiceRow {α : Type*} [DecidableEq α]
    (C : List SixSupportIndex) (f : ∀ s ∈ C.toFinset, α)
    (s : SixSupportIndex) (hsC : s ∈ C.toFinset) :
    f s hsC ∈ sixChoiceRow ⟨C, f⟩ := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨⟨s, hsC⟩, Finset.mem_attach _ _, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Elaborating the dependent choice fibers exceeds the default budget.
theorem sixChoiceRow_supportIndices {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    {q : Σ C : List SixSupportIndex, ∀ s ∈ C.toFinset, α}
    (hq : q ∈ sixActualChoices J rowOrder) :
    (sixChoiceRow q).image (sixActualSupportIndex rowOrder) = q.1.toFinset := by
  classical
  obtain ⟨_hCover, hPi⟩ := Finset.mem_sigma.mp hq
  ext s
  constructor
  · intro hsImage
    obtain ⟨x, hxRow, hxIndex⟩ := Finset.mem_image.mp hsImage
    obtain ⟨t, htAttach, htx⟩ := Finset.mem_image.mp hxRow
    have htC : t.1 ∈ q.1.toFinset := t.2
    have htFiber := Finset.mem_pi.mp hPi t.1 htC
    have htIndex : sixActualSupportIndex rowOrder (q.2 t.1 htC) = t.1 :=
      (Finset.mem_filter.mp htFiber).2
    have hst : s = t.1 := by
      calc
        s = sixActualSupportIndex rowOrder x := hxIndex.symm
        _ = sixActualSupportIndex rowOrder (q.2 t.1 htC) := by rw [htx]
        _ = t.1 := htIndex
    exact hst ▸ htC
  · intro hsC
    have hsFiber := Finset.mem_pi.mp hPi s hsC
    have hsIndex : sixActualSupportIndex rowOrder (q.2 s hsC) = s :=
      (Finset.mem_filter.mp hsFiber).2
    apply Finset.mem_image.mpr
    refine ⟨q.2 s hsC, sixChosenPoint_mem_choiceRow q.1 q.2 s hsC, hsIndex⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Equality of dependent choice functions exceeds the default elaboration budget.
theorem sixChoiceRow_injective {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H) :
    Set.InjOn sixChoiceRow (↑(sixActualChoices J rowOrder) :
      Set (Σ C : List SixSupportIndex, ∀ s ∈ C.toFinset, α)) := by
  classical
  rintro ⟨C, f⟩ hq ⟨D, g⟩ hr hRows
  have hC := (Finset.mem_sigma.mp hq).1
  have hD := (Finset.mem_sigma.mp hr).1
  have hCDsets : C.toFinset = D.toFinset := by
    calc
      C.toFinset = (sixChoiceRow ⟨C, f⟩).image (sixActualSupportIndex rowOrder) :=
        (sixChoiceRow_supportIndices rowOrder hq).symm
      _ = (sixChoiceRow ⟨D, g⟩).image (sixActualSupportIndex rowOrder) := by rw [hRows]
      _ = D.toFinset := sixChoiceRow_supportIndices rowOrder hr
  have hCD : C = D := six_minimal_support_covers_toFinset_injective hC hD hCDsets
  subst D
  have hfg : f = g := by
    funext s hsC
    have hfPi := (Finset.mem_sigma.mp hq).2
    have hgPi := (Finset.mem_sigma.mp hr).2
    have hfFiber := Finset.mem_pi.mp hfPi s hsC
    have hfIndex : sixActualSupportIndex rowOrder (f s hsC) = s :=
      (Finset.mem_filter.mp hfFiber).2
    have hfRow : f s hsC ∈ sixChoiceRow ⟨C, f⟩ :=
      sixChosenPoint_mem_choiceRow C f s hsC
    have hfRowG : f s hsC ∈ sixChoiceRow ⟨C, g⟩ := by
      rw [← hRows]
      exact hfRow
    obtain ⟨t, htAttach, htg⟩ := Finset.mem_image.mp hfRowG
    have htC : t.1 ∈ C.toFinset := t.2
    have hgFiber := Finset.mem_pi.mp hgPi t.1 htC
    have hgIndex : sixActualSupportIndex rowOrder (g t.1 htC) = t.1 :=
      (Finset.mem_filter.mp hgFiber).2
    have hts : t.1 = s := by
      calc
        t.1 = sixActualSupportIndex rowOrder (g t.1 htC) := hgIndex.symm
        _ = sixActualSupportIndex rowOrder (f s hsC) := by
          simpa using congrArg (sixActualSupportIndex rowOrder) htg
        _ = s := hfIndex
    have ht : t = ⟨s, hsC⟩ := Subtype.ext hts
    subst t
    simpa using htg.symm
  exact congrArg (Sigma.mk C) hfg

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Expanding the dependent choice fibers exceeds the default elaboration budget.
theorem sixChoiceRow_mem_blocker {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2)
    {q : Σ C : List SixSupportIndex, ∀ s ∈ C.toFinset, α}
    (hq : q ∈ sixActualChoices J rowOrder) :
    sixChoiceRow q ∈ blocker H := by
  classical
  obtain ⟨hCoverList, hPi⟩ := Finset.mem_sigma.mp hq
  have hCover : sixMinimalSupportCover q.1.toFinset :=
    six_minimal_support_covers_sound (List.mem_toFinset.mp hCoverList)
  have hTransversal : IsTransversal H (sixChoiceRow q) := by
    intro E hEH
    let e : H := ⟨E, hEH⟩
    obtain ⟨v, hv⟩ := rowOrder.surjective e
    obtain ⟨s, hsC, hvs⟩ := hCover.1 v
    have hsFiber := Finset.mem_pi.mp hPi s hsC
    obtain ⟨hsJ, hsIndex⟩ := Finset.mem_filter.mp hsFiber
    refine ⟨q.2 s hsC, sixChosenPoint_mem_choiceRow q.1 q.2 s hsC, ?_⟩
    have hSupport :=
      sixSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hsJ
    have hvSupport : v ∈ sixSupportOfPoint rowOrder (q.2 s hsC) := by
      rw [← hSupport, hsIndex]
      exact hvs
    have hxOrdered := (mem_sixSupportOfPoint rowOrder (q.2 s hsC) v).mp hvSupport
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
    exists_private_vertex_of_sixMinimalSupportCover hCover hsC
  let E : G413.Row α := rowOrder v
  refine ⟨E, (rowOrder v).property, hxRow, ?_, ?_⟩
  · rw [← hsx]
    apply (mem_sixSupportOfPoint rowOrder (q.2 s.1 hsC) v).mp
    have hSupport :=
      sixSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hsJ
    rw [← hSupport, hsIndex]
    exact hvs
  · intro y hyRow hyE
    obtain ⟨t, htAttach, hty⟩ := Finset.mem_image.mp hyRow
    have htC : t.1 ∈ q.1.toFinset := t.2
    have htFiber := Finset.mem_pi.mp hPi t.1 htC
    obtain ⟨htJ, htIndex⟩ := Finset.mem_filter.mp htFiber
    have hvtSupportPoint : v ∈ sixSupportOfPoint rowOrder (q.2 t.1 htC) := by
      apply (mem_sixSupportOfPoint rowOrder (q.2 t.1 htC) v).mpr
      simpa [E] using hty ▸ hyE
    have hSupport :=
      sixSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree htJ
    have hvt : v ∈ sixSupport t.1 := by
      rw [← htIndex, hSupport]
      exact hvtSupportPoint
    have hts : t.1 = s.1 := hvPrivate t.1 htC hvt
    have ht : t = s := Subtype.ext hts
    subst t
    simpa using hty.symm.trans hsx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The certificate lift combines all dependent choice and cardinality bounds.
theorem sixRow_lowDegree_blocker_card_ge_fifteen {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α}
    (hHcard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hMaxDegree : MaxDegreeAtMost H 2) :
    15 ≤ (blocker H).card := by
  classical
  obtain ⟨J, hCore, hMinimal⟩ := exists_minimal_three_core hHRows
  let rowOrder := sixCoreRowOrder hHcard J
  have hAtLeastThree : 3 ≤ (lowCoreRows H J).card :=
    lowCoreRows_card_ge_three_of_six hHcard hCore hMinimal hMaxDegree
  have hHigh : (lowCoreRows H J).card ≤ 6 :=
    lowCoreRows_card_le_six hHcard J
  have hValid : SixMultiplicityValid (lowCoreRows H J).card
      (sixActualSupportMultiplicity J rowOrder) := by
    simpa [rowOrder] using
      sixActualSupportMultiplicity_valid hHcard hCore hMinimal hMaxDegree
  have hLow : 4 ≤ (lowCoreRows H J).card := by
    by_contra hNotFour
    have hThree : (lowCoreRows H J).card = 3 := by omega
    rw [hThree] at hValid
    exact sixMultiplicityValid_low_three_impossible
      (sixSupportFiber J rowOrder 0).card
      (sixSupportFiber J rowOrder 1).card
      (sixSupportFiber J rowOrder 2).card
      (sixSupportFiber J rowOrder 3).card
      (sixSupportFiber J rowOrder 4).card
      (sixSupportFiber J rowOrder 5).card
      (sixSupportFiber J rowOrder 6).card
      (sixSupportFiber J rowOrder 7).card
      (sixSupportFiber J rowOrder 8).card
      (sixSupportFiber J rowOrder 9).card
      (sixSupportFiber J rowOrder 10).card
      (sixSupportFiber J rowOrder 11).card
      (sixSupportFiber J rowOrder 12).card
      (sixSupportFiber J rowOrder 13).card
      (sixSupportFiber J rowOrder 14).card
      (sixSupportFiber J rowOrder 15).card
      (sixSupportFiber J rowOrder 16).card
      (sixSupportFiber J rowOrder 17).card
      (sixSupportFiber J rowOrder 18).card
      (sixSupportFiber J rowOrder 19).card
      (sixSupportFiber J rowOrder 20).card
      (by simpa [sixActualSupportMultiplicity] using hValid)
  have hWeighted :
      15 ≤ sixWeightedCoverCount (sixActualSupportMultiplicity J rowOrder) := by
    have hCertificate := six_support_multigraph_weighted_cover_count_ge_fifteen
      (lowCoreRows H J).card
      (sixSupportFiber J rowOrder 0).card
      (sixSupportFiber J rowOrder 1).card
      (sixSupportFiber J rowOrder 2).card
      (sixSupportFiber J rowOrder 3).card
      (sixSupportFiber J rowOrder 4).card
      (sixSupportFiber J rowOrder 5).card
      (sixSupportFiber J rowOrder 6).card
      (sixSupportFiber J rowOrder 7).card
      (sixSupportFiber J rowOrder 8).card
      (sixSupportFiber J rowOrder 9).card
      (sixSupportFiber J rowOrder 10).card
      (sixSupportFiber J rowOrder 11).card
      (sixSupportFiber J rowOrder 12).card
      (sixSupportFiber J rowOrder 13).card
      (sixSupportFiber J rowOrder 14).card
      (sixSupportFiber J rowOrder 15).card
      (sixSupportFiber J rowOrder 16).card
      (sixSupportFiber J rowOrder 17).card
      (sixSupportFiber J rowOrder 18).card
      (sixSupportFiber J rowOrder 19).card
      (sixSupportFiber J rowOrder 20).card
      hLow hHigh (by simpa [sixActualSupportMultiplicity] using hValid)
    simpa [sixActualSupportMultiplicity] using hCertificate
  have hImageSubset :
      (sixActualChoices J rowOrder).image sixChoiceRow ⊆ blocker H := by
    intro T hT
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
    exact sixChoiceRow_mem_blocker rowOrder hCore hMinimal hMaxDegree hq
  calc
    15 ≤ sixWeightedCoverCount (sixActualSupportMultiplicity J rowOrder) := hWeighted
    _ = (sixActualChoices J rowOrder).card := (sixActualChoices_card J rowOrder).symm
    _ = ((sixActualChoices J rowOrder).image sixChoiceRow).card :=
      (Finset.card_image_iff.mpr (sixChoiceRow_injective rowOrder)).symm
    _ ≤ (blocker H).card := Finset.card_le_card hImageSubset

theorem sixTen_lowDegree_impossible {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α}
    (hHcard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBcard : (blocker H).card = 10)
    (hMaxDegree : MaxDegreeAtMost H 2) : False := by
  have hLower := sixRow_lowDegree_blocker_card_ge_fifteen hHcard hHRows hMaxDegree
  omega

end AiMathLab.P0054.G417
