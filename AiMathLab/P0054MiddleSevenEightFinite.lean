import AiMathLab.P0054FanoStep
import AiMathLab.P0054G420.MiddleFourDegreeFourBridge

/-!
# The finite seven-plus-eight certificate

The only tight four-row multiplicity profile is the `K₄` profile.  Its
seven-row lifted base is the Fano plane.  Closed computation identifies the
profile and checks its initial blocker; the extra-row case is discharged by
the structural Fano argument in `P0054FanoStep`.
-/

namespace AiMathLab.P0054.MiddleSevenEightFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420

def sevenEightFanoBase : G413.Hypergraph MiddleFourModelPoint :=
  middleFourDegreeFourVector20Base0.toFinset

def sevenEightFanoActive : G413.Row MiddleFourModelPoint :=
  middleFourDegreeFourVector20Eligible0.toFinset

theorem sevenEight_k4_zero_base :
    sevenEightZeroBase sevenEightK4Values =
      middleFourDegreeFourVector20Base0 := by
  rw [sevenEight_k4_eq_vector20]
  exact middleFourDegreeFourVector20_base0

theorem sevenEight_fano_base_card : sevenEightFanoBase.card = 7 := by
  decide

theorem sevenEight_fano_rows :
    ∀ E ∈ sevenEightFanoBase, E.card = 3 := by
  simp [sevenEightFanoBase, middleFourDegreeFourVector20Base0]

theorem sevenEight_fano_pairs :
    ∀ E ∈ sevenEightFanoBase, ∀ F ∈ sevenEightFanoBase,
      E ≠ F → (E ∩ F).card = 1 := by
  simp [sevenEightFanoBase, middleFourDegreeFourVector20Base0]

theorem sevenEight_fano_rows_active :
    ∀ E ∈ sevenEightFanoBase, E ⊆ sevenEightFanoActive := by
  simp [sevenEightFanoBase, sevenEightFanoActive,
    middleFourDegreeFourVector20Base0,
    middleFourDegreeFourVector20Eligible0]
  decide

theorem sevenEight_mem_fano_active_iff
    (point : MiddleFourModelPoint) :
    point ∈ sevenEightFanoActive ↔ point.val ≤ 6 := by
  fin_cases point <;> decide

def sevenEightFanoTransversalCheck : Bool :=
  (middleFourListPowerset middleFourDegreeFourVector20Eligible0).all fun old ↦
    !(middleFourDegreeFourVector20Base0.all fun L ↦
      decide (¬Disjoint old.toFinset L)) ||
      middleFourDegreeFourVector20Base0.any fun L ↦
        decide (L ⊆ old.toFinset)

theorem sevenEight_fano_transversal_check :
    sevenEightFanoTransversalCheck = true := by
  decide

theorem sevenEight_fano_transversal_contains_line :
    ∀ O ∈ sevenEightFanoActive.powerset,
      (∀ L ∈ sevenEightFanoBase, ¬Disjoint O L) →
        ∃ L ∈ sevenEightFanoBase, L ⊆ O := by
  intro O hO hMeet
  have hEnumerated : O ∈
      ((middleFourListPowerset middleFourDegreeFourVector20Eligible0).map
        List.toFinset).toFinset := by
    rw [middleFourListPowerset_toFinset]
    simpa [sevenEightFanoActive] using hO
  obtain ⟨old, hOld, hOldEq⟩ := List.mem_map.mp
    (List.mem_toFinset.mp hEnumerated)
  subst O
  have hOuter := List.all_eq_true.mp
    sevenEight_fano_transversal_check old hOld
  have hMeetBool :
      middleFourDegreeFourVector20Base0.all
        (fun L ↦ decide (¬Disjoint old.toFinset L)) = true := by
    apply List.all_eq_true.mpr
    intro L hL
    apply decide_eq_true
    exact hMeet L (by simpa [sevenEightFanoBase] using hL)
  have hAny :
      middleFourDegreeFourVector20Base0.any
        (fun L ↦ decide (L ⊆ old.toFinset)) = true := by
    change (!middleFourDegreeFourVector20Base0.all
        (fun L ↦ decide (¬Disjoint old.toFinset L)) ||
      middleFourDegreeFourVector20Base0.any
        (fun L ↦ decide (L ⊆ old.toFinset))) = true at hOuter
    rw [hMeetBool] at hOuter
    simpa using hOuter
  obtain ⟨L, hL, hSubset⟩ := List.any_eq_true.mp hAny
  exact ⟨L, by simpa [sevenEightFanoBase] using hL,
    of_decide_eq_true hSubset⟩

theorem sevenEight_fano_self_blocker :
    blocker sevenEightFanoBase = sevenEightFanoBase := by
  classical
  have hBaseBlocker : sevenEightFanoBase ⊆ blocker sevenEightFanoBase := by
    intro L hL
    apply mem_blocker.mpr
    apply isMinimalTransversal_iff.mpr
    constructor
    · intro E hE
      by_cases hEL : E = L
      · subst E
        obtain ⟨point, hPoint⟩ : L.Nonempty :=
          Finset.card_pos.mp (by rw [sevenEight_fano_rows L hL]; omega)
        exact ⟨point, hPoint, hPoint⟩
      · have hInter := sevenEight_fano_pairs E hE L hL hEL
        obtain ⟨point, hPoint⟩ : (E ∩ L).Nonempty :=
          Finset.card_pos.mp (by omega)
        exact ⟨point, (Finset.mem_inter.mp hPoint).2,
          (Finset.mem_inter.mp hPoint).1⟩
    · intro O hProper hOTransversal
      have hOPowerset : O ∈ sevenEightFanoActive.powerset := by
        rw [Finset.mem_powerset]
        exact hProper.1.trans (sevenEight_fano_rows_active L hL)
      have hMeet : ∀ E ∈ sevenEightFanoBase, ¬Disjoint O E := by
        intro E hE hDisjoint
        obtain ⟨point, hPointO, hPointE⟩ := hOTransversal E hE
        exact Finset.disjoint_left.mp hDisjoint hPointO hPointE
      obtain ⟨M, hM, hMO⟩ :=
        sevenEight_fano_transversal_contains_line O hOPowerset hMeet
      have hML : M ⊆ L := hMO.trans hProper.1
      have hMEqL : M = L := by
        apply Finset.eq_of_subset_of_card_le hML
        rw [sevenEight_fano_rows M hM, sevenEight_fano_rows L hL]
      exact hProper.2 (hMEqL ▸ hMO)
  apply Finset.Subset.antisymm
  · intro R hR
    have hRActive : R ∈ sevenEightFanoActive.powerset := by
      rw [Finset.mem_powerset]
      intro point hPoint
      obtain ⟨L, hL, hPointL⟩ := Finset.mem_biUnion.mp
        (blocker_row_subset_biUnion hR hPoint)
      exact sevenEight_fano_rows_active L hL hPointL
    have hMeet : ∀ L ∈ sevenEightFanoBase, ¬Disjoint R L := by
      intro L hL hDisjoint
      obtain ⟨point, hPointR, hPointL⟩ := (mem_blocker.mp hR).prop L hL
      exact Finset.disjoint_left.mp hDisjoint hPointR hPointL
    obtain ⟨L, hL, hLR⟩ :=
      sevenEight_fano_transversal_contains_line R hRActive hMeet
    have hEq : L = R :=
      (blocker_isClutter sevenEightFanoBase) (hBaseBlocker hL) hR hLR
    simpa [hEq] using hL
  · exact hBaseBlocker

theorem sevenEight_fano_exists_disjoint_of_clutter
    {R : G413.Row MiddleFourModelPoint}
    (hClutter : IsClutter (insert R sevenEightFanoBase))
    (hRNotBase : R ∉ sevenEightFanoBase) :
    ∃ L ∈ sevenEightFanoBase, Disjoint L R := by
  by_contra hNoDisjoint
  push_neg at hNoDisjoint
  let O := R ∩ sevenEightFanoActive
  have hOPowerset : O ∈ sevenEightFanoActive.powerset := by
    rw [Finset.mem_powerset]
    exact Finset.inter_subset_right
  have hMeet : ∀ L ∈ sevenEightFanoBase, ¬Disjoint O L := by
    intro L hL hOL
    exact hNoDisjoint L hL (by
      rw [Finset.disjoint_left]
      intro x hxL hxR
      have hxActive := sevenEight_fano_rows_active L hL hxL
      exact Finset.disjoint_left.mp hOL
        (Finset.mem_inter.mpr ⟨hxR, hxActive⟩) hxL)
  obtain ⟨L, hL, hLO⟩ :=
    sevenEight_fano_transversal_contains_line O hOPowerset hMeet
  have hLR : L ⊆ R := hLO.trans Finset.inter_subset_left
  have hEq : L = R := hClutter (by simp [hL]) (by simp) hLR
  apply hRNotBase
  simpa [← hEq] using hL

theorem sevenEight_candidate_valid
    {R : G413.Row MiddleFourModelPoint}
    (hValid : middleFourModelCandidateRowsValid
      (R :: middleFourDegreeFourVector20Base0) = true) :
    IsClutter (insert R sevenEightFanoBase) ∧ 3 ≤ R.card := by
  unfold middleFourModelCandidateRowsValid at hValid
  have hBoth := Bool.and_eq_true_iff.mp hValid
  constructor
  · unfold sevenEightFanoBase IsClutter
    simpa only [List.toFinset_cons] using
      (of_decide_eq_true hBoth.1)
  · have hRow := List.all_eq_true.mp hBoth.2 R (by simp)
    exact (of_decide_eq_true hRow).1

theorem sevenEight_k4_extra_step
    {R : G413.Row MiddleFourModelPoint}
    (hValid : middleFourModelCandidateRowsValid
      (R :: middleFourDegreeFourVector20Base0) = true)
    (hRNotBase : R ∉ sevenEightFanoBase) :
    (fastBlockerStep sevenEightFanoBase R).card ≠ 7 := by
  obtain ⟨hClutter, hRCard⟩ := sevenEight_candidate_valid hValid
  have hDisjoint := sevenEight_fano_exists_disjoint_of_clutter
    hClutter hRNotBase
  have hLarge := FanoStep.seven_lt_fastBlockerStep
    sevenEight_fano_base_card sevenEight_fano_rows
      sevenEight_fano_pairs hRCard hDisjoint
  omega

theorem sevenEight_actual_values_eq_k4 {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α} (rowOrder : Fin 4 ≃ K)
    (hKClutter : IsClutter K)
    (hBKRows : RowsCardAtLeast (blocker K) 2)
    (hKRows : RowsCardAtLeast K 3)
    (hKUpper : ∀ E ∈ K, E.card ≤ 8)
    (hBKCard : (blocker K).card ≤ 8)
    (hPairCard : (pairRows (blocker K)).card ≤ 3) :
    (fourActualSupportMultiplicity rowOrder).toList = sevenEightK4Values := by
  have hCertificate := middleFourActualSupportMultiplicity_in_certificate
    rowOrder hKClutter hBKRows hKRows hKUpper
      hBKCard (hPairCard.trans (by omega))
  have hProfile := middleFourActualSupportMultiplicity_profile
    rowOrder hKClutter hBKRows hKRows hKUpper
      hBKCard (hPairCard.trans (by omega))
  have hPairBound :=
    (fourPairCoverCount_le_pairRows_card rowOrder hBKRows).trans hPairCard
  unfold middleFourMultiplicityInCertificate at hCertificate
  obtain ⟨values, hValues, hListCheck⟩ := List.any_eq_true.mp hCertificate
  have hList : (fourActualSupportMultiplicity rowOrder).toList = values :=
    of_decide_eq_true hListCheck
  have hArray : values.toArray = fourActualSupportMultiplicity rowOrder := by
    rw [← hList]
  have hSeven :
      fourWeightedCoverCount (fourActualSupportMultiplicity rowOrder) = 7 ∧
        fourPairCoverCount (fourActualSupportMultiplicity rowOrder) = 3 := by
    rcases hProfile with hEight | hSeven
    · omega
    · exact hSeven
  have hEq : values = sevenEightK4Values :=
    sevenEight_certificate_eq_k4 values hValues
      (by simpa [hArray] using hSeven.1)
      (by simpa [hArray] using hSeven.2)
  exact hList.trans hEq

theorem sevenEight_actual_base_checks {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α} (rowOrder : Fin 4 ≃ K)
    (hKClutter : IsClutter K)
    (hBKRows : RowsCardAtLeast (blocker K) 2)
    (hKRows : RowsCardAtLeast K 3)
    (hKUpper : ∀ E ∈ K, E.card ≤ 8)
    (hBKCard : (blocker K).card ≤ 8)
    (hPairCard : (pairRows (blocker K)).card ≤ 3) :
    sevenEightKernelCardCheck
          (fourActualSupportMultiplicity rowOrder).toList = true ∧
      sevenEightBaseCheck
          (fourActualSupportMultiplicity rowOrder).toList = true := by
  rw [sevenEight_actual_values_eq_k4 rowOrder hKClutter hBKRows
    hKRows hKUpper hBKCard hPairCard]
  exact ⟨sevenEight_k4_kernel_card_check,
    sevenEight_k4_base_check⟩

end AiMathLab.P0054.MiddleSevenEightFinite
