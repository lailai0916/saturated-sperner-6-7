import AiMathLab.P0054AdjacentSixActual

/-!
# Lifting the adjacent six-row certificate

The compact finite check counts choices of one actual point from every support in
a minimal support cover.  This file proves that these choices are distinct rows
of the blocker.  The hypothesis that blocker rows have size at least four also
rules out a positive three-support cover, exactly the extra condition used by
the compact check.
-/

namespace AiMathLab.P0054.AdjacentSix

open AiMathLab.P0054.G413
open AiMathLab.P0054.G416
open AiMathLab.P0054.G417
open AiMathLab.P0054.AdjacentSixFinite

-- Dependent theorem types make this naming linter exceed its heartbeat budget.
set_option linter.constructorNameAsVariable false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Expanding the dependent choice fibers exceeds the default elaboration budget.
theorem sixChoiceRow_mem_blocker_two_core {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 2)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2)
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
    have hSupport := sixSupport_actualSupportIndex_two_core rowOrder
      hCore hMinimal hMaxDegree hsJ
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
    have hSupport := sixSupport_actualSupportIndex_two_core rowOrder
      hCore hMinimal hMaxDegree hsJ
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
    have hSupport := sixSupport_actualSupportIndex_two_core rowOrder
      hCore hMinimal hMaxDegree htJ
    have hvt : v ∈ sixSupport t.1 := by
      rw [← htIndex, hSupport]
      exact hvtSupportPoint
    have hts : t.1 = s.1 := hvPrivate t.1 htC hvt
    have ht : t = s := Subtype.ext hts
    subst t
    simpa using hty.symm.trans hsx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
-- The dependent representatives turn a positive three-cover into a small blocker row.
theorem adjacentSixNoThreeCover_actual {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 2)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2)
    (hMaxDegree : MaxDegreeAtMost H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4) :
    AdjacentSixNoThreeCover (sixActualSupportMultiplicity J rowOrder) := by
  classical
  intro C hC hLength
  by_contra hNoZero
  have hPositive : ∀ s : SixSupportIndex, s ∈ C.toFinset →
      0 < sixMultiplicityDigit (sixActualSupportMultiplicity J rowOrder) s.val := by
    intro s hsC
    by_contra hNotPositive
    apply hNoZero
    refine ⟨s, List.mem_toFinset.mp hsC, Nat.eq_zero_of_not_pos hNotPositive⟩
  let hFiber : ∀ s : SixSupportIndex, s ∈ C.toFinset →
      (sixSupportFiber J rowOrder s).Nonempty := fun s hsC ↦
    Finset.card_pos.mp (by
      rw [← sixMultiplicityDigit_actualSupportMultiplicity J rowOrder s]
      exact hPositive s hsC)
  let f : ∀ s : SixSupportIndex, s ∈ C.toFinset → α :=
    fun s hsC ↦ (hFiber s hsC).choose
  let q : Σ D : List SixSupportIndex, ∀ s ∈ D.toFinset, α := ⟨C, f⟩
  have hq : q ∈ sixActualChoices J rowOrder := by
    apply Finset.mem_sigma.mpr
    refine ⟨List.mem_toFinset.mpr hC, ?_⟩
    apply Finset.mem_pi.mpr
    intro s hsC
    exact Classical.choose_spec (hFiber s hsC)
  have hBlocker : sixChoiceRow q ∈ blocker H :=
    sixChoiceRow_mem_blocker_two_core rowOrder hCore hMinimal hMaxDegree hq
  have hAtLeastFour : 4 ≤ (sixChoiceRow q).card := hBRows _ hBlocker
  have hAtMostThree : (sixChoiceRow q).card ≤ 3 := by
    calc
      (sixChoiceRow q).card ≤ C.toFinset.attach.card := by
        exact Finset.card_image_le
      _ = C.toFinset.card := by simp
      _ ≤ C.length := List.toFinset_card_le C
      _ = 3 := hLength
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- The checked weighted count is lifted injectively to actual blocker rows.
theorem sixRow_lowDegree_blocker_card_ge_six_two_core {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α}
    (hHcard : H.card = 6)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4)
    (hMaxDegree : MaxDegreeAtMost H 2) :
    6 ≤ (blocker H).card := by
  classical
  obtain ⟨J, hCore, hMinimal⟩ := exists_minimal_two_core hHRows
  let rowOrder := sixTwoCoreRowOrder hHcard J
  have hLow : 1 ≤ (lowTwoCoreRows H J).card :=
    lowTwoCoreRows_card_pos hHcard hCore hMinimal
  have hHigh : (lowTwoCoreRows H J).card ≤ 6 :=
    lowTwoCoreRows_card_le_six hHcard J
  have hValid : AdjacentSixMultiplicityValid (lowTwoCoreRows H J).card
      (sixActualSupportMultiplicity J rowOrder) := by
    simpa [rowOrder] using
      sixActualMultiplicity_valid_two_core hHcard hCore hMinimal hMaxDegree
  have hNoThree : AdjacentSixNoThreeCover
      (sixActualSupportMultiplicity J rowOrder) :=
    adjacentSixNoThreeCover_actual rowOrder hCore hMinimal hMaxDegree hBRows
  let hValidExists : ∃ lowCount,
      AdjacentSixMultiplicityValid lowCount (sixActualSupportMultiplicity J rowOrder) :=
    ⟨(lowTwoCoreRows H J).card, hValid⟩
  let target := adjacentSixTargetOfMultiplicity
    (sixActualSupportMultiplicity J rowOrder) hValidExists
  have hReconstruct : adjacentSixMultiplicityOfFunction target =
      sixActualSupportMultiplicity J rowOrder := by
    apply adjacentSixMultiplicityOf_target
    exact sixActualSupportMultiplicity_size J rowOrder
  have hTargetValid : AdjacentSixMultiplicityValid (lowTwoCoreRows H J).card
      (adjacentSixMultiplicityOfFunction target) := by
    rw [hReconstruct]
    exact hValid
  have hTargetNoThree : AdjacentSixNoThreeCover
      (adjacentSixMultiplicityOfFunction target) := by
    rw [hReconstruct]
    exact hNoThree
  have hWeighted : 6 ≤ sixWeightedCoverCount
      (sixActualSupportMultiplicity J rowOrder) := by
    have hChecked := adjacent_six_compact_check_sound hLow hHigh target
      hTargetValid hTargetNoThree
    simpa [hReconstruct] using hChecked
  have hImageSubset :
      (sixActualChoices J rowOrder).image sixChoiceRow ⊆ blocker H := by
    intro T hT
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
    exact sixChoiceRow_mem_blocker_two_core rowOrder hCore hMinimal hMaxDegree hq
  calc
    6 ≤ sixWeightedCoverCount (sixActualSupportMultiplicity J rowOrder) := hWeighted
    _ = (sixActualChoices J rowOrder).card :=
      (sixActualChoices_card J rowOrder).symm
    _ = ((sixActualChoices J rowOrder).image sixChoiceRow).card :=
      (Finset.card_image_iff.mpr (sixChoiceRow_injective rowOrder)).symm
    _ ≤ (blocker H).card := Finset.card_le_card hImageSubset

end AiMathLab.P0054.AdjacentSix
