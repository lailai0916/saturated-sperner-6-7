import AiMathLab.P0054G416.SupportMultigraphActual
import AiMathLab.P0054G417.SupportMultigraphBounds

namespace AiMathLab.P0054.G417

open G413
open G416
open scoped BigOperators

theorem sixSupport_injective : Function.Injective sixSupport := by
  decide

set_option maxRecDepth 100000 in
theorem sixSupport_complete :
    ∀ S : Finset SixVertex, S.Nonempty → S.card ≤ 2 →
      ∃ s : SixSupportIndex, sixSupport s = S := by
  decide

theorem sixSupport_existsUnique_of_nonempty_card_le_two
    (S : Finset SixVertex) (hS : S.Nonempty) (hCard : S.card ≤ 2) :
    ∃! s : SixSupportIndex, sixSupport s = S := by
  obtain ⟨s, hs⟩ := sixSupport_complete S hS hCard
  exact ⟨s, hs, fun t ht ↦ sixSupport_injective (ht.trans hs.symm)⟩

noncomputable def sixSupportIndexOf (S : Finset SixVertex) : SixSupportIndex :=
  if h : S.Nonempty ∧ S.card ≤ 2 then
    (sixSupport_existsUnique_of_nonempty_card_le_two S h.1 h.2).choose
  else 0

theorem sixSupport_indexOf {S : Finset SixVertex}
    (hS : S.Nonempty) (hCard : S.card ≤ 2) :
    sixSupport (sixSupportIndexOf S) = S := by
  rw [sixSupportIndexOf, dif_pos ⟨hS, hCard⟩]
  exact (sixSupport_existsUnique_of_nonempty_card_le_two S hS hCard).choose_spec.1

def sixSupportOfPoint {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (rowOrder : Fin 6 ≃ H) (x : α) : Finset SixVertex :=
  Finset.univ.filter fun v ↦ x ∈ (rowOrder v : G413.Row α)

theorem mem_sixSupportOfPoint {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (rowOrder : Fin 6 ≃ H) (x : α) (v : SixVertex) :
    v ∈ sixSupportOfPoint rowOrder x ↔ x ∈ (rowOrder v : G413.Row α) := by
  simp [sixSupportOfPoint]

theorem sixSupportOfPoint_card {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (rowOrder : Fin 6 ≃ H) (x : α) :
    (sixSupportOfPoint rowOrder x).card = degree H x := by
  classical
  rw [degree]
  apply Finset.card_bij (fun v _ ↦ (rowOrder v : G413.Row α))
  · intro v hv
    exact Finset.mem_filter.mpr ⟨(rowOrder v).property,
      (mem_sixSupportOfPoint rowOrder x v).mp hv⟩
  · intro v hv w hw hEq
    exact rowOrder.injective (Subtype.ext hEq)
  · intro E hE
    obtain ⟨hEH, hxE⟩ := Finset.mem_filter.mp hE
    let e : H := ⟨E, hEH⟩
    refine ⟨rowOrder.symm e, ?_, ?_⟩
    · exact (mem_sixSupportOfPoint rowOrder x _).mpr (by simpa [e] using hxE)
    · simp [e]

noncomputable def sixCoreRowOrder {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 6) (J : Finset α) : Fin 6 ≃ H :=
  firstEquivOfFinset (lowCoreRows H J) (by simpa using hHcard)

theorem sixCoreRowOrder_low_iff {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 6) (J : Finset α) (v : Fin 6) :
    sixCoreRowOrder hHcard J v ∈ lowCoreRows H J ↔
      v.val < (lowCoreRows H J).card := by
  exact firstEquivOfFinset_mem_iff (lowCoreRows H J) (by simpa using hHcard) v

theorem lowCoreRows_card_ge_three_of_six {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hHcard : H.card = 6)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2) :
    3 ≤ (lowCoreRows H J).card := by
  have hIncidenceLower : 18 ≤ coreIncidenceCount H J := by
    calc
      18 = ∑ E ∈ H.attach, 3 := by simp [hHcard]
      _ ≤ coreIncidenceCount H J := by
        unfold coreIncidenceCount
        apply Finset.sum_le_sum
        intro E hEH
        exact hCore E E.property
  have hIncidenceUpper : coreIncidenceCount H J ≤ J.card * 2 := by
    rw [coreIncidenceCount_eq_sum_degree]
    calc
      (∑ x ∈ J, degree H x) ≤ ∑ _x ∈ J, 2 := by
        apply Finset.sum_le_sum
        intro x hxJ
        exact hMaxDegree x
      _ = J.card * 2 := by simp
  have hCoreCard := core_card_le_low_count_mul_three hCore hMinimal
  by_contra hLow
  have hAtMostTwo : (lowCoreRows H J).card ≤ 2 := by omega
  omega

theorem lowCoreRows_card_le_six {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 6) (J : Finset α) :
    (lowCoreRows H J).card ≤ 6 := by
  calc
    (lowCoreRows H J).card ≤ H.attach.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 6 := by simpa using hHcard

theorem sixSupportOfPoint_nonempty_of_mem_core {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    {x : α} (hxJ : x ∈ J) :
    (sixSupportOfPoint rowOrder x).Nonempty := by
  obtain ⟨E, hEH, hxE, hECard⟩ :=
    exists_degree_three_row_through_core_point hCore hMinimal hxJ
  let e : H := ⟨E, hEH⟩
  obtain ⟨v, hv⟩ := rowOrder.surjective e
  refine ⟨v, (mem_sixSupportOfPoint rowOrder x v).mpr ?_⟩
  simpa [e, hv] using hxE

noncomputable def sixActualSupportIndex {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (rowOrder : Fin 6 ≃ H) (x : α) : SixSupportIndex :=
  sixSupportIndexOf (sixSupportOfPoint rowOrder x)

noncomputable def sixSupportFiber {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 6 ≃ H)
    (s : SixSupportIndex) : Finset α :=
  J.filter fun x ↦ sixActualSupportIndex rowOrder x = s

noncomputable def sixActualSupportMultiplicity {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 6 ≃ H) :
    SixMultiplicity :=
  sixMultiplicityOfValues
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

theorem sixMultiplicityDigit_actualSupportMultiplicity {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 6 ≃ H)
    (s : SixSupportIndex) :
    sixMultiplicityDigit (sixActualSupportMultiplicity J rowOrder) s.val =
      (sixSupportFiber J rowOrder s).card := by
  fin_cases s <;>
    simp [sixActualSupportMultiplicity, sixMultiplicityDigit, sixMultiplicityOfValues]

theorem sixSupport_actualSupportIndex {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2)
    {x : α} (hxJ : x ∈ J) :
    sixSupport (sixActualSupportIndex rowOrder x) = sixSupportOfPoint rowOrder x := by
  apply sixSupport_indexOf
  · exact sixSupportOfPoint_nonempty_of_mem_core rowOrder hCore hMinimal hxJ
  · rw [sixSupportOfPoint_card]
    exact hMaxDegree x

theorem sixSupportDegree_actualSupportMultiplicity {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 6 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2)
    (v : SixVertex) :
    sixSupportDegree (sixActualSupportMultiplicity J rowOrder) v =
      ((rowOrder v : G413.Row α).filter fun x ↦ x ∈ J).card := by
  classical
  let rowPoints : Finset α :=
    J.filter fun x ↦ v ∈ sixSupportOfPoint rowOrder x
  have hPartition := Finset.card_eq_sum_card_fiberwise
    (s := rowPoints) (t := (Finset.univ : Finset SixSupportIndex))
    (f := sixActualSupportIndex rowOrder) (by simp)
  rw [show ((rowOrder v : G413.Row α).filter fun x ↦ x ∈ J) = rowPoints by
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
      have hSupport := sixSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hxJ
      have hvx : v ∈ sixSupportOfPoint rowOrder x := by
        rw [← hSupport, hxs]
        exact hvs
      exact ⟨⟨hxJ, hvx⟩, hxs⟩
    · rintro ⟨⟨hxJ, _hvx⟩, hxs⟩
      exact ⟨hxJ, hxs⟩
  · simp only [hvs, if_false]
    symm
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxRowPoints, hxs⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxJ, hvx⟩ := Finset.mem_filter.mp hxRowPoints
    have hSupport := sixSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hxJ
    apply hvs
    rw [← hxs, hSupport]
    exact hvx

theorem sixActualSupportMultiplicity_valid {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hHcard : H.card = 6)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2) :
    SixMultiplicityValid (lowCoreRows H J).card
      (sixActualSupportMultiplicity J (sixCoreRowOrder hHcard J)) := by
  classical
  let rowOrder := sixCoreRowOrder hHcard J
  constructor
  · intro v
    rw [sixSupportDegree_actualSupportMultiplicity rowOrder hCore hMinimal hMaxDegree]
    split_ifs with hv
    · have hLow : rowOrder v ∈ lowCoreRows H J :=
        (sixCoreRowOrder_low_iff hHcard J v).mpr hv
      exact (Finset.mem_filter.mp hLow).2
    · have hAtLeast := hCore (rowOrder v : G413.Row α) (rowOrder v).property
      have hNotThree :
          ((rowOrder v : G413.Row α).filter fun x ↦ x ∈ J).card ≠ 3 := by
        intro hThree
        apply hv
        apply (sixCoreRowOrder_low_iff hHcard J v).mp
        exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hThree⟩
      omega
  · intro s hPositive
    rw [sixMultiplicityDigit_actualSupportMultiplicity] at hPositive
    obtain ⟨x, hxFiber⟩ := Finset.card_pos.mp hPositive
    obtain ⟨hxJ, hxIndex⟩ := Finset.mem_filter.mp hxFiber
    obtain ⟨E, hEH, hxE, hECard⟩ :=
      exists_degree_three_row_through_core_point hCore hMinimal hxJ
    let e : H := ⟨E, hEH⟩
    obtain ⟨v, hv⟩ := rowOrder.surjective e
    refine ⟨v, ?_, ?_⟩
    · have hSupport :=
        sixSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hxJ
      rw [← hxIndex, hSupport]
      apply (mem_sixSupportOfPoint rowOrder x v).mpr
      simpa [e, hv] using hxE
    · apply (sixCoreRowOrder_low_iff hHcard J v).mp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_attach _ _, ?_⟩
      have hRow : (rowOrder v : G413.Row α) = E := by
        simpa [e] using congrArg Subtype.val hv
      rw [hRow]
      exact hECard

end AiMathLab.P0054.G417
