import AiMathLab.P0054AdjacentSixCompactSound
import AiMathLab.P0054AdjacentLower

/-!
# The actual two-core support multigraph for six rows

This file constructs the support multiplicity vector of a minimal two-core and
proves that it satisfies the hypotheses of the checked adjacent certificate.
-/

namespace AiMathLab.P0054.AdjacentSix

open AiMathLab.P0054.G413
open AiMathLab.P0054.G416
open AiMathLab.P0054.G417
open AiMathLab.P0054.AdjacentSixFinite

theorem exists_minimal_two_core {α : Type*} [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hRows : RowsCardAtLeast H 2) :
    ∃ J : Finset α,
      RowsMeetCardAtLeast H J 2 ∧
      ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2 := by
  classical
  have hUniv : RowsMeetCardAtLeast H Finset.univ 2 := by
    intro E hEH
    simpa using hRows E hEH
  obtain ⟨J, -, hJ⟩ :=
    exists_minimal_le_of_wellFoundedLT (fun K : Finset α ↦ RowsMeetCardAtLeast H K 2)
      Finset.univ hUniv
  refine ⟨J, hJ.prop, ?_⟩
  intro K hK hKRows
  exact hK.2 (hJ.le_of_le hKRows hK.1)

theorem exists_degree_two_row_through_core_point {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hCore : RowsMeetCardAtLeast H J 2)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2)
    {x : α} (hxJ : x ∈ J) :
    ∃ E : Row α, E ∈ H ∧ x ∈ E ∧ (E.filter fun y ↦ y ∈ J).card = 2 := by
  classical
  have hErase : ¬RowsMeetCardAtLeast H (J.erase x) 2 :=
    hMinimal (J.erase x) (Finset.erase_ssubset hxJ)
  simp only [RowsMeetCardAtLeast] at hErase
  push Not at hErase
  obtain ⟨E, hEH, hSmall⟩ := hErase
  have hxE : x ∈ E := by
    by_contra hxE
    have hEq : E.filter (fun y ↦ y ∈ J.erase x) = E.filter (fun y ↦ y ∈ J) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hyE, -, hyJ⟩
        exact ⟨hyE, hyJ⟩
      · rintro ⟨hyE, hyJ⟩
        exact ⟨hyE, fun hyx ↦ hxE (hyx ▸ hyE), hyJ⟩
    rw [hEq] at hSmall
    exact Nat.not_lt_of_ge (hCore E hEH) hSmall
  have hFilterErase :
      E.filter (fun y ↦ y ∈ J.erase x) = (E.filter fun y ↦ y ∈ J).erase x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  have hxFilter : x ∈ E.filter (fun y ↦ y ∈ J) :=
    Finset.mem_filter.mpr ⟨hxE, hxJ⟩
  rw [hFilterErase, Finset.card_erase_of_mem hxFilter] at hSmall
  refine ⟨E, hEH, hxE, ?_⟩
  have hLarge := hCore E hEH
  omega

def lowTwoCoreRows {α : Type*} [DecidableEq α]
    (H : G413.Hypergraph α) (J : Finset α) : Finset H :=
  H.attach.filter fun E ↦ ((E : Row α).filter fun x ↦ x ∈ J).card = 2

noncomputable def sixTwoCoreRowOrder {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 6) (J : Finset α) : Fin 6 ≃ H :=
  firstEquivOfFinset (lowTwoCoreRows H J) (by simpa using hHcard)

theorem sixTwoCoreRowOrder_low_iff {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 6) (J : Finset α) (v : Fin 6) :
    sixTwoCoreRowOrder hHcard J v ∈ lowTwoCoreRows H J ↔
      v.val < (lowTwoCoreRows H J).card := by
  exact firstEquivOfFinset_mem_iff (lowTwoCoreRows H J) (by simpa using hHcard) v

theorem lowTwoCoreRows_card_pos {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hHcard : H.card = 6)
    (hCore : RowsMeetCardAtLeast H J 2)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2) :
    1 ≤ (lowTwoCoreRows H J).card := by
  have hHNonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨E, hEH⟩ := hHNonempty
  have hIntersection : 2 ≤ (E.filter fun x ↦ x ∈ J).card := hCore E hEH
  obtain ⟨x, hx⟩ : (E.filter fun x ↦ x ∈ J).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hxJ := (Finset.mem_filter.mp hx).2
  obtain ⟨P, hPH, hxP, hPCard⟩ :=
    exists_degree_two_row_through_core_point hCore hMinimal hxJ
  apply Finset.card_pos.mpr
  exact ⟨⟨P, hPH⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hPCard⟩⟩

theorem lowTwoCoreRows_card_le_six {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 6) (J : Finset α) :
    (lowTwoCoreRows H J).card ≤ 6 := by
  calc
    (lowTwoCoreRows H J).card ≤ H.attach.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 6 := by simpa using hHcard

theorem sixSupportOfPoint_nonempty_two_core {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 2)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2)
    {x : α} (hxJ : x ∈ J) :
    (sixSupportOfPoint rowOrder x).Nonempty := by
  obtain ⟨E, hEH, hxE, hECard⟩ :=
    exists_degree_two_row_through_core_point hCore hMinimal hxJ
  let e : H := ⟨E, hEH⟩
  obtain ⟨v, hv⟩ := rowOrder.surjective e
  refine ⟨v, (mem_sixSupportOfPoint rowOrder x v).mpr ?_⟩
  simpa [e, hv] using hxE

theorem sixSupport_actualSupportIndex_two_core {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 2)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2)
    (hMaxDegree : MaxDegreeAtMost H 2)
    {x : α} (hxJ : x ∈ J) :
    sixSupport (sixActualSupportIndex rowOrder x) = sixSupportOfPoint rowOrder x := by
  apply sixSupport_indexOf
  · exact sixSupportOfPoint_nonempty_two_core rowOrder hCore hMinimal hxJ
  · rw [sixSupportOfPoint_card]
    exact hMaxDegree x

theorem sixSupportDegree_actualMultiplicity_two_core {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 2)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2)
    (hMaxDegree : MaxDegreeAtMost H 2)
    (v : SixVertex) :
    sixSupportDegree (sixActualSupportMultiplicity J rowOrder) v =
      ((rowOrder v : Row α).filter fun x ↦ x ∈ J).card := by
  classical
  let rowPoints : Finset α :=
    J.filter fun x ↦ v ∈ sixSupportOfPoint rowOrder x
  have hPartition := Finset.card_eq_sum_card_fiberwise
    (s := rowPoints) (t := (Finset.univ : Finset SixSupportIndex))
    (f := sixActualSupportIndex rowOrder) (by simp)
  rw [show ((rowOrder v : Row α).filter fun x ↦ x ∈ J) = rowPoints by
    ext x
    simp [rowPoints, mem_sixSupportOfPoint, and_comm]]
  rw [hPartition]
  unfold sixSupportDegree
  apply Finset.sum_congr rfl
  intro s hs
  rw [sixMultiplicityDigit_actualSupportMultiplicity]
  by_cases hvs : v ∈ sixSupport s
  · simp only [hvs, if_true]
    congr 1
    ext x
    simp only [Finset.mem_filter, sixSupportFiber, rowPoints]
    constructor
    · rintro ⟨hxJ, hxs⟩
      have hSupport := sixSupport_actualSupportIndex_two_core rowOrder
        hCore hMinimal hMaxDegree hxJ
      have hvx : v ∈ sixSupportOfPoint rowOrder x := by
        rw [← hSupport, hxs]
        exact hvs
      exact ⟨⟨hxJ, hvx⟩, hxs⟩
    · rintro ⟨⟨hxJ, _⟩, hxs⟩
      exact ⟨hxJ, hxs⟩
  · simp only [hvs, if_false]
    symm
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxRowPoints, hxs⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxJ, hvx⟩ := Finset.mem_filter.mp hxRowPoints
    have hSupport := sixSupport_actualSupportIndex_two_core rowOrder
      hCore hMinimal hMaxDegree hxJ
    apply hvs
    rw [← hxs, hSupport]
    exact hvx

theorem sixActualMultiplicity_valid_two_core {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hHcard : H.card = 6)
    (hCore : RowsMeetCardAtLeast H J 2)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 2)
    (hMaxDegree : MaxDegreeAtMost H 2) :
    AdjacentSixMultiplicityValid (lowTwoCoreRows H J).card
      (sixActualSupportMultiplicity J (sixTwoCoreRowOrder hHcard J)) := by
  classical
  let rowOrder := sixTwoCoreRowOrder hHcard J
  constructor
  · intro v
    rw [sixSupportDegree_actualMultiplicity_two_core rowOrder
      hCore hMinimal hMaxDegree]
    split_ifs with hv
    · have hLow : rowOrder v ∈ lowTwoCoreRows H J :=
        (sixTwoCoreRowOrder_low_iff hHcard J v).mpr hv
      exact (Finset.mem_filter.mp hLow).2
    · have hAtLeast := hCore (rowOrder v : Row α) (rowOrder v).property
      have hNotTwo : ((rowOrder v : Row α).filter fun x ↦ x ∈ J).card ≠ 2 := by
        intro hTwo
        apply hv
        apply (sixTwoCoreRowOrder_low_iff hHcard J v).mp
        exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hTwo⟩
      omega
  · intro s hPositive
    rw [sixMultiplicityDigit_actualSupportMultiplicity] at hPositive
    obtain ⟨x, hxFiber⟩ := Finset.card_pos.mp hPositive
    obtain ⟨hxJ, hxIndex⟩ := Finset.mem_filter.mp hxFiber
    obtain ⟨E, hEH, hxE, hECard⟩ :=
      exists_degree_two_row_through_core_point hCore hMinimal hxJ
    let e : H := ⟨E, hEH⟩
    obtain ⟨v, hv⟩ := rowOrder.surjective e
    refine ⟨v, ?_, ?_⟩
    · have hSupport := sixSupport_actualSupportIndex_two_core rowOrder
        hCore hMinimal hMaxDegree hxJ
      rw [← hxIndex, hSupport]
      apply (mem_sixSupportOfPoint rowOrder x v).mpr
      simpa [e, hv] using hxE
    · apply (sixTwoCoreRowOrder_low_iff hHcard J v).mp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_attach _ _, ?_⟩
      have hRow : (rowOrder v : Row α) = E := by
        simpa [e] using congrArg Subtype.val hv
      rw [hRow]
      exact hECard

theorem adjacentSixMultiplicityDigit_lt_three_of_valid
    {lowCount : Nat} {m : SixMultiplicity}
    (hValid : AdjacentSixMultiplicityValid lowCount m) (s : SixSupportIndex) :
    sixMultiplicityDigit m s.val < 3 := by
  by_cases hZero : sixMultiplicityDigit m s.val = 0
  · omega
  have hPositive : 0 < sixMultiplicityDigit m s.val := Nat.pos_of_ne_zero hZero
  obtain ⟨v, hvs, hvLow⟩ := hValid.2 s hPositive
  have hDegree := hValid.1 v
  rw [if_pos hvLow] at hDegree
  have hTerm : sixMultiplicityDigit m s.val ≤ sixSupportDegree m v := by
    unfold sixSupportDegree
    have hSingle := Finset.single_le_sum
      (s := (Finset.univ : Finset SixSupportIndex))
      (f := fun t : SixSupportIndex ↦
        if v ∈ sixSupport t then sixMultiplicityDigit m t.val else 0)
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ s)
    simpa [hvs] using hSingle
  omega

noncomputable def adjacentSixTargetOfMultiplicity
    (m : SixMultiplicity) (hValid : ∃ lowCount, AdjacentSixMultiplicityValid lowCount m) :
    Fin 21 → Fin 3 := fun s ↦
  ⟨sixMultiplicityDigit m s.val,
    adjacentSixMultiplicityDigit_lt_three_of_valid hValid.choose_spec s⟩

theorem adjacentSixMultiplicityOf_target
    (m : SixMultiplicity) (hSize : m.size = 21)
    (hValid : ∃ lowCount, AdjacentSixMultiplicityValid lowCount m) :
    adjacentSixMultiplicityOfFunction (adjacentSixTargetOfMultiplicity m hValid) = m := by
  apply Array.ext
  · simp [adjacentSixMultiplicityOfFunction, hSize]
  · intro i hiLeft hiRight
    have hi : i < 21 := by simpa [adjacentSixMultiplicityOfFunction] using hiLeft
    simp [adjacentSixMultiplicityOfFunction, adjacentSixTargetOfMultiplicity,
      sixMultiplicityDigit, Array.getD, hiRight]

theorem sixActualSupportMultiplicity_size {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 6 ≃ H) :
    (sixActualSupportMultiplicity J rowOrder).size = 21 := by
  simp [sixActualSupportMultiplicity, sixMultiplicityOfValues]

end AiMathLab.P0054.AdjacentSix
