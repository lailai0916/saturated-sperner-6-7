import AiMathLab.P0054G416.SupportMultigraphBounds

namespace AiMathLab.P0054.G416

open G413
open scoped BigOperators

def RowsMeetCardAtLeast {α : Type*} [DecidableEq α]
    (H : G413.Hypergraph α) (J : Finset α) (n : Nat) : Prop :=
  ∀ E : G413.Row α, E ∈ H → n ≤ (E.filter fun x ↦ x ∈ J).card

theorem exists_minimal_three_core {α : Type*} [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hRows : RowsCardAtLeast H 3) :
    ∃ J : Finset α,
      RowsMeetCardAtLeast H J 3 ∧
      ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3 := by
  classical
  have hUniv : RowsMeetCardAtLeast H Finset.univ 3 := by
    intro E hEH
    simpa using hRows E hEH
  obtain ⟨J, -, hJ⟩ :=
    exists_minimal_le_of_wellFoundedLT (fun K : Finset α ↦ RowsMeetCardAtLeast H K 3)
      Finset.univ hUniv
  refine ⟨J, hJ.prop, ?_⟩
  intro K hK hKRows
  exact hK.2 (hJ.le_of_le hKRows hK.1)

theorem exists_degree_three_row_through_core_point {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    {x : α} (hxJ : x ∈ J) :
    ∃ E : G413.Row α, E ∈ H ∧ x ∈ E ∧ (E.filter fun y ↦ y ∈ J).card = 3 := by
  classical
  have hErase : ¬RowsMeetCardAtLeast H (J.erase x) 3 :=
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
    exact (Nat.not_lt_of_ge (hCore E hEH) hSmall)
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

theorem fiveSupport_injective : Function.Injective fiveSupport := by
  decide

theorem fiveSupport_exists_of_nonempty_card_le_two
    (S : Finset FiveVertex) (hS : S.Nonempty) (hCard : S.card ≤ 2) :
    ∃ s : FiveSupportIndex, fiveSupport s = S := by
  have hCardCases : S.card = 1 ∨ S.card = 2 := by
    have hPositive := Finset.card_pos.mpr hS
    omega
  rcases hCardCases with hOne | hTwo
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hOne
    fin_cases v
    all_goals
      solve
      | exact ⟨0, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨2, by decide⟩
      | exact ⟨3, by decide⟩
      | exact ⟨4, by decide⟩
  · obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hTwo
    fin_cases v <;> fin_cases w <;> simp_all
    all_goals
      solve
      | exact ⟨5, by decide⟩
      | exact ⟨6, by decide⟩
      | exact ⟨7, by decide⟩
      | exact ⟨8, by decide⟩
      | exact ⟨9, by decide⟩
      | exact ⟨10, by decide⟩
      | exact ⟨11, by decide⟩
      | exact ⟨12, by decide⟩
      | exact ⟨13, by decide⟩
      | exact ⟨14, by decide⟩

theorem fiveSupport_existsUnique_of_nonempty_card_le_two
    (S : Finset FiveVertex) (hS : S.Nonempty) (hCard : S.card ≤ 2) :
    ∃! s : FiveSupportIndex, fiveSupport s = S := by
  obtain ⟨s, hs⟩ := fiveSupport_exists_of_nonempty_card_le_two S hS hCard
  exact ⟨s, hs, fun t ht ↦ fiveSupport_injective (ht.trans hs.symm)⟩

noncomputable def fiveSupportIndexOf (S : Finset FiveVertex) : FiveSupportIndex :=
  if h : S.Nonempty ∧ S.card ≤ 2 then
    (fiveSupport_existsUnique_of_nonempty_card_le_two S h.1 h.2).choose
  else 0

theorem fiveSupport_indexOf {S : Finset FiveVertex}
    (hS : S.Nonempty) (hCard : S.card ≤ 2) :
    fiveSupport (fiveSupportIndexOf S) = S := by
  rw [fiveSupportIndexOf, dif_pos ⟨hS, hCard⟩]
  exact (fiveSupport_existsUnique_of_nonempty_card_le_two S hS hCard).choose_spec.1

def supportOfPoint {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (rowOrder : Fin 5 ≃ H) (x : α) : Finset FiveVertex :=
  Finset.univ.filter fun v ↦ x ∈ (rowOrder v : G413.Row α)

theorem mem_supportOfPoint {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (rowOrder : Fin 5 ≃ H) (x : α) (v : FiveVertex) :
    v ∈ supportOfPoint rowOrder x ↔ x ∈ (rowOrder v : G413.Row α) := by
  simp [supportOfPoint]

theorem supportOfPoint_card {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (rowOrder : Fin 5 ≃ H) (x : α) :
    (supportOfPoint rowOrder x).card = degree H x := by
  classical
  rw [degree]
  apply Finset.card_bij (fun v _ ↦ (rowOrder v : G413.Row α))
  · intro v hv
    exact Finset.mem_filter.mpr ⟨(rowOrder v).property,
      (mem_supportOfPoint rowOrder x v).mp hv⟩
  · intro v hv w hw hEq
    exact rowOrder.injective (Subtype.ext hEq)
  · intro E hE
    obtain ⟨hEH, hxE⟩ := Finset.mem_filter.mp hE
    let e : H := ⟨E, hEH⟩
    refine ⟨rowOrder.symm e, ?_, ?_⟩
    · exact (mem_supportOfPoint rowOrder x _).mpr (by simpa [e] using hxE)
    · simp [e]

noncomputable def firstEquivOfFinset {β : Type*} [Fintype β]
    (s : Finset β) {n : Nat} (hCard : Fintype.card β = n) : Fin n ≃ β := by
  classical
  have hLe : s.card ≤ n := by
    rw [← hCard]
    exact Finset.card_le_univ s
  have hSum : s.card + (n - s.card) = n := Nat.add_sub_of_le hLe
  let lowEquiv : Fin s.card ≃ {x : β // x ∈ s} :=
    (s.equivFinOfCardEq rfl).symm
  have hHighCard : Fintype.card {x : β // x ∉ s} = n - s.card := by
    rw [Fintype.card_subtype_compl, hCard, Fintype.card_coe]
  let highEquiv : Fin (n - s.card) ≃ {x : β // x ∉ s} :=
    (Fintype.equivFinOfCardEq hHighCard).symm
  exact (finCongr hSum).symm |>.trans <|
    finSumFinEquiv.symm |>.trans <|
    (Equiv.sumCongr lowEquiv highEquiv).trans (Equiv.sumCompl fun x ↦ x ∈ s)

theorem firstEquivOfFinset_mem_iff {β : Type*} [Fintype β]
    (s : Finset β) {n : Nat} (hCard : Fintype.card β = n) (v : Fin n) :
    firstEquivOfFinset s hCard v ∈ s ↔ v.val < s.card := by
  classical
  let z : Fin (s.card + (n - s.card)) :=
    (finCongr (Nat.add_sub_of_le (by
      rw [← hCard]
      exact Finset.card_le_univ s))).symm v
  have hHighCard : Fintype.card {x : β // x ∉ s} = n - s.card := by
    rw [Fintype.card_subtype_compl, hCard, Fintype.card_coe]
  generalize hz : finSumFinEquiv.symm z = q
  cases q with
  | inl a =>
    have hz' : z = Fin.castAdd (n - s.card) a := by
      calc
        z = finSumFinEquiv (finSumFinEquiv.symm z) :=
          (finSumFinEquiv.apply_symm_apply z).symm
        _ = Fin.castAdd (n - s.card) a := by simp [hz]
    have hv : v.val = a.val := by
      have hzVal := congrArg Fin.val hz'
      simpa [z] using hzVal
    simp only [firstEquivOfFinset, Equiv.trans_apply]
    rw [show (finCongr _).symm v = z by rfl, hz]
    simp [hv, a.isLt]
  | inr b =>
    have hz' : z = Fin.natAdd s.card b := by
      calc
        z = finSumFinEquiv (finSumFinEquiv.symm z) :=
          (finSumFinEquiv.apply_symm_apply z).symm
        _ = Fin.natAdd s.card b := by simp [hz]
    have hv : v.val = s.card + b.val := by
      have hzVal := congrArg Fin.val hz'
      simpa [z] using hzVal
    simp only [firstEquivOfFinset, Equiv.trans_apply]
    rw [show (finCongr _).symm v = z by rfl, hz]
    simp only [Equiv.sumCongr_apply, Equiv.sumCompl_apply_inr, Sum.map_inr, hv]
    constructor
    · intro hMem
      exact (((Fintype.equivFinOfCardEq hHighCard).symm b).property hMem).elim
    · intro hLt
      omega

def lowCoreRows {α : Type*} [DecidableEq α]
    (H : G413.Hypergraph α) (J : Finset α) : Finset H :=
  H.attach.filter fun E ↦ ((E : G413.Row α).filter fun x ↦ x ∈ J).card = 3

noncomputable def coreRowOrder {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 5) (J : Finset α) : Fin 5 ≃ H :=
  firstEquivOfFinset (lowCoreRows H J) (by simpa using hHcard)

theorem coreRowOrder_low_iff {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 5) (J : Finset α) (v : Fin 5) :
    coreRowOrder hHcard J v ∈ lowCoreRows H J ↔
      v.val < (lowCoreRows H J).card := by
  exact firstEquivOfFinset_mem_iff (lowCoreRows H J) (by simpa using hHcard) v

def coreIncidenceCount {α : Type*} [DecidableEq α]
    (H : G413.Hypergraph α) (J : Finset α) : Nat :=
  ∑ E ∈ H.attach, ((E : G413.Row α).filter fun x ↦ x ∈ J).card

theorem attach_filter_card_eq_degree {α : Type*} [DecidableEq α]
    (H : G413.Hypergraph α) (x : α) :
    (H.attach.filter fun E : H ↦ x ∈ (E : G413.Row α)).card = degree H x := by
  rw [degree]
  apply Finset.card_bij
    (s := H.attach.filter fun E : H ↦ x ∈ (E : G413.Row α))
    (t := H.filter fun E ↦ x ∈ E)
    (fun E _ ↦ (E : G413.Row α))
  · intro E hE
    exact Finset.mem_filter.mpr ⟨E.property, (Finset.mem_filter.mp hE).2⟩
  · intro E hE F hF hEq
    exact Subtype.ext hEq
  · intro E hE
    obtain ⟨hEH, hxE⟩ := Finset.mem_filter.mp hE
    refine ⟨⟨E, hEH⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hxE⟩

theorem coreIncidenceCount_eq_sum_degree {α : Type*} [DecidableEq α]
    (H : G413.Hypergraph α) (J : Finset α) :
    coreIncidenceCount H J = ∑ x ∈ J, degree H x := by
  classical
  calc
    coreIncidenceCount H J =
        ∑ E ∈ H.attach, ∑ x ∈ J, if x ∈ (E : G413.Row α) then 1 else 0 := by
      unfold coreIncidenceCount
      apply Finset.sum_congr rfl
      intro E hEH
      rw [Finset.sum_boole]
      congr 1
      ext x
      simp only [Finset.mem_filter]
      tauto
    _ = ∑ x ∈ J, ∑ E ∈ H.attach,
        if x ∈ (E : G413.Row α) then 1 else 0 := Finset.sum_comm
    _ = ∑ x ∈ J, degree H x := by
      apply Finset.sum_congr rfl
      intro x hxJ
      rw [Finset.sum_boole]
      exact attach_filter_card_eq_degree H x

theorem core_card_le_low_count_mul_three {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3) :
    J.card ≤ (lowCoreRows H J).card * 3 := by
  classical
  let covered : Finset α :=
    (lowCoreRows H J).biUnion fun E ↦
      (E : G413.Row α).filter fun x ↦ x ∈ J
  have hSubset : J ⊆ covered := by
    intro x hxJ
    obtain ⟨E, hEH, hxE, hECard⟩ :=
      exists_degree_three_row_through_core_point hCore hMinimal hxJ
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨E, hEH⟩, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hECard⟩
    · exact Finset.mem_filter.mpr ⟨hxE, hxJ⟩
  calc
    J.card ≤ covered.card := Finset.card_le_card hSubset
    _ ≤ ∑ E ∈ lowCoreRows H J,
        ((E : G413.Row α).filter fun x ↦ x ∈ J).card := Finset.card_biUnion_le
    _ = (lowCoreRows H J).card * 3 := by
      apply Finset.sum_const_nat
      intro E hE
      exact (Finset.mem_filter.mp hE).2

theorem lowCoreRows_card_ge_three {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hHcard : H.card = 5)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2) :
    3 ≤ (lowCoreRows H J).card := by
  have hIncidenceLower : 15 ≤ coreIncidenceCount H J := by
    calc
      15 = ∑ E ∈ H.attach, 3 := by simp [hHcard]
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

theorem lowCoreRows_card_le_five {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (hHcard : H.card = 5) (J : Finset α) :
    (lowCoreRows H J).card ≤ 5 := by
  calc
    (lowCoreRows H J).card ≤ H.attach.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 5 := by simpa using hHcard

theorem supportOfPoint_nonempty_of_mem_core {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 5 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    {x : α} (hxJ : x ∈ J) :
    (supportOfPoint rowOrder x).Nonempty := by
  obtain ⟨E, hEH, hxE, hECard⟩ :=
    exists_degree_three_row_through_core_point hCore hMinimal hxJ
  let e : H := ⟨E, hEH⟩
  obtain ⟨v, hv⟩ := rowOrder.surjective e
  refine ⟨v, (mem_supportOfPoint rowOrder x v).mpr ?_⟩
  simpa [e, hv] using hxE

noncomputable def actualSupportIndex {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (rowOrder : Fin 5 ≃ H) (x : α) : FiveSupportIndex :=
  fiveSupportIndexOf (supportOfPoint rowOrder x)

noncomputable def supportFiber {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 5 ≃ H)
    (s : FiveSupportIndex) : Finset α :=
  J.filter fun x ↦ actualSupportIndex rowOrder x = s

noncomputable def actualSupportMultiplicity {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 5 ≃ H) :
    FiveMultiplicity :=
  fiveMultiplicityOfValues
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

theorem fiveMultiplicityDigit_actualSupportMultiplicity {α : Type*} [DecidableEq α]
    {H : G413.Hypergraph α} (J : Finset α) (rowOrder : Fin 5 ≃ H)
    (s : FiveSupportIndex) :
    fiveMultiplicityDigit (actualSupportMultiplicity J rowOrder) s.val =
      (supportFiber J rowOrder s).card := by
  fin_cases s <;>
    simp [actualSupportMultiplicity, fiveMultiplicityDigit, fiveMultiplicityOfValues]

theorem fiveSupport_actualSupportIndex {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 5 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2)
    {x : α} (hxJ : x ∈ J) :
    fiveSupport (actualSupportIndex rowOrder x) = supportOfPoint rowOrder x := by
  apply fiveSupport_indexOf
  · exact supportOfPoint_nonempty_of_mem_core rowOrder hCore hMinimal hxJ
  · rw [supportOfPoint_card]
    exact hMaxDegree x

theorem fiveSupportDegree_actualSupportMultiplicity {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (rowOrder : Fin 5 ≃ H)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2)
    (v : FiveVertex) :
    fiveSupportDegree (actualSupportMultiplicity J rowOrder) v =
      ((rowOrder v : G413.Row α).filter fun x ↦ x ∈ J).card := by
  classical
  let rowPoints : Finset α :=
    J.filter fun x ↦ v ∈ supportOfPoint rowOrder x
  have hPartition := Finset.card_eq_sum_card_fiberwise
    (s := rowPoints) (t := (Finset.univ : Finset FiveSupportIndex))
    (f := actualSupportIndex rowOrder) (by simp)
  rw [show ((rowOrder v : G413.Row α).filter fun x ↦ x ∈ J) = rowPoints by
    ext x
    simp [rowPoints, mem_supportOfPoint, and_comm]]
  rw [hPartition]
  unfold fiveSupportDegree
  apply Finset.sum_congr rfl
  intro s hs
  rw [fiveMultiplicityDigit_actualSupportMultiplicity]
  by_cases hvs : v ∈ fiveSupport s
  · simp only [hvs, if_true]
    congr 1
    ext x
    simp only [Finset.mem_filter, supportFiber, rowPoints]
    constructor
    · rintro ⟨hxJ, hxs⟩
      have hSupport := fiveSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hxJ
      have hvx : v ∈ supportOfPoint rowOrder x := by
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
    have hSupport := fiveSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hxJ
    apply hvs
    rw [← hxs, hSupport]
    exact hvx

theorem actualSupportMultiplicity_valid {α : Type*}
    [Fintype α] [DecidableEq α] {H : G413.Hypergraph α} {J : Finset α}
    (hHcard : H.card = 5)
    (hCore : RowsMeetCardAtLeast H J 3)
    (hMinimal : ∀ K : Finset α, K ⊂ J → ¬RowsMeetCardAtLeast H K 3)
    (hMaxDegree : MaxDegreeAtMost H 2) :
    FiveMultiplicityValid (lowCoreRows H J).card
      (actualSupportMultiplicity J (coreRowOrder hHcard J)) := by
  classical
  let rowOrder := coreRowOrder hHcard J
  constructor
  · intro v
    rw [fiveSupportDegree_actualSupportMultiplicity rowOrder hCore hMinimal hMaxDegree]
    split_ifs with hv
    · have hLow : rowOrder v ∈ lowCoreRows H J :=
        (coreRowOrder_low_iff hHcard J v).mpr hv
      exact (Finset.mem_filter.mp hLow).2
    · have hAtLeast := hCore (rowOrder v : G413.Row α) (rowOrder v).property
      have hNotThree :
          ((rowOrder v : G413.Row α).filter fun x ↦ x ∈ J).card ≠ 3 := by
        intro hThree
        apply hv
        apply (coreRowOrder_low_iff hHcard J v).mp
        exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hThree⟩
      omega
  · intro s hPositive
    rw [fiveMultiplicityDigit_actualSupportMultiplicity] at hPositive
    obtain ⟨x, hxFiber⟩ := Finset.card_pos.mp hPositive
    obtain ⟨hxJ, hxIndex⟩ := Finset.mem_filter.mp hxFiber
    obtain ⟨E, hEH, hxE, hECard⟩ :=
      exists_degree_three_row_through_core_point hCore hMinimal hxJ
    let e : H := ⟨E, hEH⟩
    obtain ⟨v, hv⟩ := rowOrder.surjective e
    refine ⟨v, ?_, ?_⟩
    · have hSupport :=
        fiveSupport_actualSupportIndex rowOrder hCore hMinimal hMaxDegree hxJ
      rw [← hxIndex, hSupport]
      apply (mem_supportOfPoint rowOrder x v).mpr
      simpa [e, hv] using hxE
    · apply (coreRowOrder_low_iff hHcard J v).mp
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_attach _ _, ?_⟩
      have hRow : (rowOrder v : G413.Row α) = E := by
        simpa [e] using congrArg Subtype.val hv
      rw [hRow]
      exact hECard

end AiMathLab.P0054.G416
