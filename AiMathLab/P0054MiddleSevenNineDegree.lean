import AiMathLab.P0054MiddleSevenEightDegree
import AiMathLab.P0054MiddleSixProfile

/-!
# Degree bounds for the middle split seven plus nine

The preliminary residual bounds give degrees at most four on the seven-row
side and at most six on the nine-row side.  A three-row residual excludes
degree six.  Degree five on the nine-row side has the unique `K₄` kernel;
its five possible lifted bases have blocker cardinality different from nine.
Finally, the exact three-row profile excludes degree four on the seven-row
side.
-/

namespace AiMathLab.P0054.MiddleSevenNineDegree

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.MiddleSevenEightDegree

theorem sevenRows_maxDegreeAtMost_four {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 9) :
    MaxDegreeAtMost H 4 := by
  classical
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHRows
  intro x
  by_contra hNot
  have hAvoidUpper : (avoidPoint H x).card ≤ 2 := by
    have hPartition := card_avoidPoint_add_degree H x
    omega
  interval_cases hAvoidCard : (avoidPoint H x).card
  · have hTransversal : IsTransversal H {x} := by
      intro E hEH
      have hxE : x ∈ E := by
        by_contra hxE
        have hEAvoid : E ∈ avoidPoint H x :=
          mem_avoidPoint.mpr ⟨hEH, hxE⟩
        have : 0 < (avoidPoint H x).card :=
          Finset.card_pos.mpr ⟨E, hEAvoid⟩
        omega
      exact ⟨x, by simp, hxE⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  · obtain ⟨E, hAvoidEq⟩ := Finset.card_eq_one.mp hAvoidCard
    have hEAvoid : E ∈ avoidPoint H x := by simp [hAvoidEq]
    have hEH : E ∈ H := (mem_avoidPoint.mp hEAvoid).1
    obtain ⟨y, hyE⟩ : E.Nonempty :=
      Finset.card_pos.mp (by have := hHRows E hEH; omega)
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x :=
          mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoidEq] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      ((Finset.card_le_two : ({x, y} : Row α).card ≤ 2).trans_lt (by omega))
  · have hNine : 9 ≤ degree (blocker H) x :=
      AiMathLab.P0054.G415.twoAvoidingRows_blockers_containing_card_ge_nine
        hHRows hBRows hAvoidCard
    have hUpper : degree (blocker H) x ≤ (blocker H).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hDegree : degree (blocker H) x = 9 := by omega
    have hAll : ∀ E ∈ blocker H, x ∈ E := by
      intro E hE
      by_contra hxE
      have hSubset : insert E ((blocker H).filter fun R ↦ x ∈ R) ⊆ blocker H := by
        intro R hR
        rcases Finset.mem_insert.mp hR with rfl | hR
        · exact hE
        · exact (Finset.mem_filter.mp hR).1
      have hNotMem : E ∉ (blocker H).filter fun R ↦ x ∈ R := by
        simp [hxE]
      have hCardLower := Finset.card_le_card hSubset
      rw [Finset.card_insert_of_notMem hNotMem, ← degree, hDegree, hBCard]
        at hCardLower
      omega
    have hSingleton : IsTransversal (blocker H) {x} := by
      intro E hE
      exact ⟨x, by simp, hAll E hE⟩
    exact false_of_small_transversal hDualRows hSingleton (by simp)

theorem nineRows_maxDegreeAtMost_six {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHCard : H.card = 9)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7) :
    MaxDegreeAtMost H 6 := by
  classical
  intro x
  by_contra hNot
  have hAvoidUpper : (avoidPoint H x).card ≤ 2 := by
    have hPartition := card_avoidPoint_add_degree H x
    omega
  interval_cases hAvoidCard : (avoidPoint H x).card
  · have hTransversal : IsTransversal H {x} := by
      intro E hEH
      have hxE : x ∈ E := by
        by_contra hxE
        have hEAvoid : E ∈ avoidPoint H x :=
          mem_avoidPoint.mpr ⟨hEH, hxE⟩
        have : 0 < (avoidPoint H x).card :=
          Finset.card_pos.mpr ⟨E, hEAvoid⟩
        omega
      exact ⟨x, by simp, hxE⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  · obtain ⟨E, hAvoidEq⟩ := Finset.card_eq_one.mp hAvoidCard
    have hEAvoid : E ∈ avoidPoint H x := by simp [hAvoidEq]
    have hEH : E ∈ H := (mem_avoidPoint.mp hEAvoid).1
    obtain ⟨y, hyE⟩ : E.Nonempty :=
      Finset.card_pos.mp (by have := hHRows E hEH; omega)
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x :=
          mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoidEq] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      ((Finset.card_le_two : ({x, y} : Row α).card ≤ 2).trans_lt (by omega))
  · have hNine : 9 ≤ degree (blocker H) x :=
      AiMathLab.P0054.G415.twoAvoidingRows_blockers_containing_card_ge_nine
        hHRows hBRows hAvoidCard
    have hUpper : degree (blocker H) x ≤ (blocker H).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega

theorem nineRows_degreeSix_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 9)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 4)
    {x : α} (hDegree : degree H x = 6) : False := by
  let K := avoidPoint H x
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hPairUpper : (pairRows (blocker K)).card ≤ 5 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using
          pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 4 := hBMaxDegree x
      _ ≤ 5 := by omega
  have hBlockerUpper : (blocker K).card ≤ 8 := by
    have hLift := blocker_avoidPoint_card_le_blocker H x
    have : (blocker K).card ≤ 7 := by simpa [K, hBCard] using hLift
    omega
  exact threeRows_pair_five_total_eight_impossible hKClutter hKCard
    hKRows hBKRows hPairUpper hBlockerUpper

def sevenNineK4LiftBaseCheck : Bool :=
  (middleFourModelLiftSelectionRows sevenEightK4Values).all fun selected ↦
    decide ((fastBlocker
      (middleFourModelLiftBaseRows sevenEightK4Values selected)).card ≠ 9)

theorem sevenNine_k4_lift_base_check :
    sevenNineK4LiftBaseCheck = true := by
  decide

theorem nineRows_degreeFive_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 9)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 4)
    {x : α} (hDegree : degree H x = 5) : False := by
  classical
  let K := avoidPoint H x
  have hKCard : K.card = 4 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hKUpper : ∀ E ∈ K, E.card ≤ 8 := by
    intro E hEK
    have hEH : E ∈ H := (mem_avoidPoint.mp (by simpa [K] using hEK)).1
    have hEDual : E ∈ blocker (blocker H) := by
      simpa [blocker_involution hHClutter] using hEH
    have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hEDual)
    omega
  have hBKSevenUpper : (blocker K).card ≤ 7 := by
    have hLift := blocker_avoidPoint_card_le_blocker H x
    simpa [K, hBCard] using hLift
  have hBKUpper : (blocker K).card ≤ 8 := hBKSevenUpper.trans (by omega)
  have hPairUpper : (pairRows (blocker K)).card ≤ 4 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using
          pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 4 := hBMaxDegree x
  let rowOrder := fourRowOrder hKCard
  have hProfile := middleFourActualSupportMultiplicity_profile rowOrder
    hKClutter hBKRows hKRows hKUpper hBKUpper hPairUpper
  have hActualBlockerLower :=
    fourWeightedCoverCount_le_blocker_card rowOrder hBKRows
  have hBKCard : (blocker K).card = 7 := by
    rcases hProfile with hEight | hSeven
    · have hEightLower : 8 ≤ (blocker K).card := by
        rw [← hEight.1]
        exact hActualBlockerLower
      omega
    · have hSevenLower : 7 ≤ (blocker K).card := by
        rw [← hSeven.1]
        exact hActualBlockerLower
      omega
  have hValues : (fourActualSupportMultiplicity rowOrder).toList =
      sevenEightK4Values := by
    have hCertificate := middleFourActualSupportMultiplicity_in_certificate
      rowOrder hKClutter hBKRows hKRows hKUpper hBKUpper hPairUpper
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
      · have hEightLower : 8 ≤ (blocker K).card := by
          rw [← hEight.1]
          exact hActualBlockerLower
        omega
      · exact hSeven
    have hEq : values = sevenEightK4Values :=
      sevenEight_certificate_eq_k4 values hValues
        (by simpa [hArray] using hSeven.1)
        (by simpa [hArray] using hSeven.2)
    exact hList.trans hEq
  have hLength : (fourActivePoints
      (fourActualSupportMultiplicity rowOrder)).length < 16 :=
    middleFourActualPoints_length_lt_sixteen rowOrder hKClutter hBKRows
      hKRows hKUpper hBKUpper hPairUpper
  have hPairLength :
      (middleFourModelPairBlockerRows
        (fourActualSupportMultiplicity rowOrder).toList).length = 3 := by
    rw [hValues]
    decide
  have hSelectionBound := middleFourSemanticSelected_length_bound
    H x rowOrder hBRows hBKRows hLength (hBMaxDegree x)
  have hSelection : middleFourSemanticSelected H x rowOrder ∈
      middleFourModelLiftSelectionRows
        (fourActualSupportMultiplicity rowOrder).toList :=
    middleFourSemanticSelected_mem_liftSelectionRows
      H x rowOrder hSelectionBound
  have hSameCard : (blocker (avoidPoint H x)).card = (blocker H).card := by
    simpa [K, hBKCard, hBCard]
  let base := middleFourModelLiftBaseRows
    (fourActualSupportMultiplicity rowOrder).toList
    (middleFourSemanticSelected H x rowOrder)
  have hBaseBlockerCard : (blocker base.toFinset).card = 9 := by
    simpa [base, hHCard] using semanticLiftBase_blocker_card_eq_family
      x rowOrder hHClutter hBRows hBKRows hLength hSameCard
  have hCheck := List.all_eq_true.mp sevenNine_k4_lift_base_check
    (middleFourSemanticSelected H x rowOrder) (by simpa [hValues] using hSelection)
  have hNe : (fastBlocker base).card ≠ 9 := by
    simpa [sevenNineK4LiftBaseCheck, base, hValues] using
      of_decide_eq_true hCheck
  rw [fastBlocker_eq_blocker] at hNe
  exact hNe hBaseBlockerCard

theorem nineRows_maxDegreeAtMost_four {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 9)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 4) :
    MaxDegreeAtMost H 4 := by
  have hUpper := nineRows_maxDegreeAtMost_six hHCard hHRows hBRows hBCard
  intro x
  have hxUpper := hUpper x
  by_contra hNot
  by_cases hDegreeSix : degree H x = 6
  · exact nineRows_degreeSix_impossible hHClutter hHCard hHRows hBRows
      hBCard hBMaxDegree hDegreeSix
  · have hDegreeFive : degree H x = 5 := by omega
    exact nineRows_degreeFive_impossible hHClutter hHCard hHRows hBRows
      hBCard hBMaxDegree hDegreeFive

theorem profile_pair_at_least_five
    {p q r x12 x13 x23 : Nat}
    (hProfile : OrderedThreeKernelProfile p q r x12 x13 x23) :
    5 ≤ x12 * x13 + x12 * x23 + x13 * x23 +
      x12 * r + x13 * q + x23 * p := by
  unfold OrderedThreeKernelProfile at hProfile
  rcases hProfile with h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;> norm_num

theorem threeRows_pair_four_total_nine_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α}
    (hKClutter : IsClutter K)
    (hKCard : K.card = 3)
    (hKRows : RowsCardAtLeast K 3)
    (hBKRows : RowsCardAtLeast (blocker K) 2)
    (hPairUpper : (pairRows (blocker K)).card ≤ 4)
    (hBlockerUpper : (blocker K).card ≤ 9) : False := by
  classical
  obtain ⟨A, B, C, hAB, hAC, hBC, hK⟩ := Finset.card_eq_three.mp hKCard
  have hNoCommon : ∀ u, ¬(u ∈ A ∧ u ∈ B ∧ u ∈ C) :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hK hBKRows
  have hAK : A ∈ K := by simp [hK]
  have hBK : B ∈ K := by simp [hK]
  have hCK : C ∈ K := by simp [hK]
  have hAnotB : ¬A ⊆ B := fun h ↦ hAB (hKClutter hAK hBK h)
  have hBnotA : ¬B ⊆ A := fun h ↦ hAB (hKClutter hBK hAK h).symm
  have hAnotC : ¬A ⊆ C := fun h ↦ hAC (hKClutter hAK hCK h)
  have hCnotA : ¬C ⊆ A := fun h ↦ hAC (hKClutter hCK hAK h).symm
  have hBnotC : ¬B ⊆ C := fun h ↦ hBC (hKClutter hBK hCK h)
  have hCnotB : ¬C ⊆ B := fun h ↦ hBC (hKClutter hCK hBK h).symm
  have hPY : 0 < (privatePart A B C).card + (sharedPart A C B).card := by
    obtain ⟨u, huA, huB⟩ := Finset.not_subset.mp hAnotB
    by_cases huC : u ∈ C
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huC⟩, huB⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huA, by simp [huB, huC]⟩⟩) _
  have hQZ : 0 < (privatePart B A C).card + (sharedPart B C A).card := by
    obtain ⟨u, huB, huA⟩ := Finset.not_subset.mp hBnotA
    by_cases huC : u ∈ C
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huB, huC⟩, huA⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huB, by simp [huA, huC]⟩⟩) _
  have hPX : 0 < (privatePart A B C).card + (sharedPart A B C).card := by
    obtain ⟨u, huA, huC⟩ := Finset.not_subset.mp hAnotC
    by_cases huB : u ∈ B
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huB⟩, huC⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huA, by simp [huB, huC]⟩⟩) _
  have hRZ : 0 < (privatePart C A B).card + (sharedPart B C A).card := by
    obtain ⟨u, huC, huA⟩ := Finset.not_subset.mp hCnotA
    by_cases huB : u ∈ B
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huB, huC⟩, huA⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huC, by simp [huA, huB]⟩⟩) _
  have hQX : 0 < (privatePart B A C).card + (sharedPart A B C).card := by
    obtain ⟨u, huB, huC⟩ := Finset.not_subset.mp hBnotC
    by_cases huA : u ∈ A
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huB⟩, huC⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huB, by simp [huA, huC]⟩⟩) _
  have hRY : 0 < (privatePart C A B).card + (sharedPart A C B).card := by
    obtain ⟨u, huC, huB⟩ := Finset.not_subset.mp hCnotB
    by_cases huA : u ∈ A
    · exact Nat.add_pos_right _ (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨huA, huC⟩, huB⟩⟩)
    · exact Nat.add_pos_left (Finset.card_pos.mpr ⟨u,
        Finset.mem_sdiff.mpr ⟨huC, by simp [huA, huB]⟩⟩) _
  have hACard := hKRows A hAK
  have hBCard := hKRows B hBK
  have hCCard := hKRows C hCK
  rw [threePart_union_card hNoCommon] at hACard
  rw [threePart_union_card_second hNoCommon] at hBCard
  rw [threePart_union_card_third hNoCommon] at hCCard
  have hPair :
      (sharedPart A B C).card * (sharedPart A C B).card +
        (sharedPart A B C).card * (sharedPart B C A).card +
        (sharedPart A C B).card * (sharedPart B C A).card +
        (sharedPart A B C).card * (privatePart C A B).card +
        (sharedPart A C B).card * (privatePart B A C).card +
        (sharedPart B C A).card * (privatePart A B C).card ≤ 4 :=
    (threePairGenerated_card_le_pairRows hK).trans hPairUpper
  have hTotal :
      (sharedPart A B C).card * (sharedPart A C B).card +
        (sharedPart A B C).card * (sharedPart B C A).card +
        (sharedPart A C B).card * (sharedPart B C A).card +
        (sharedPart A B C).card * (privatePart C A B).card +
        (sharedPart A C B).card * (privatePart B A C).card +
        (sharedPart B C A).card * (privatePart A B C).card +
        (privatePart A B C).card * (privatePart B A C).card *
          (privatePart C A B).card ≤ 9 :=
    (threeGeneratedRows_card_le_blocker hK hAB hAC hBC).trans hBlockerUpper
  have hProfile := orderedThreeKernelProfile_of_bounds
    (privatePart A B C).card (privatePart B A C).card
    (privatePart C A B).card (sharedPart A B C).card
    (sharedPart A C B).card (sharedPart B C A).card
    hACard hBCard hCCard hPY hQZ hPX hRZ hQX hRY
    (hPair.trans (by omega)) (hTotal.trans (by omega))
  have hFive := profile_pair_at_least_five hProfile
  omega

theorem sevenRows_degreeFour_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 9)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 4)
    {x : α} (hDegree : degree H x = 4) : False := by
  classical
  let K := avoidPoint H x
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hPairUpper : (pairRows (blocker K)).card ≤ 4 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using
          pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 4 := hBMaxDegree x
  have hKernelUpper : (blocker K).card ≤ 9 := by
    simpa [K, hBCard] using blocker_avoidPoint_card_le_blocker H x
  exact threeRows_pair_four_total_nine_impossible hKClutter hKCard
    hKRows hBKRows hPairUpper hKernelUpper

theorem middle_maxDegrees {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 9) :
    MaxDegreeAtMost H 3 ∧ MaxDegreeAtMost (blocker H) 4 := by
  have hHFour := sevenRows_maxDegreeAtMost_four
    hHClutter hHCard hHRows hBRows hBCard
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHRows
  have hDualCard : (blocker (blocker H)).card = 7 := by
    simpa [blocker_involution hHClutter] using hHCard
  have hDualFour : MaxDegreeAtMost (blocker (blocker H)) 4 := by
    simpa [blocker_involution hHClutter] using hHFour
  have hBFour := nineRows_maxDegreeAtMost_four
    (blocker_isClutter H) hBCard hBRows hDualRows hDualCard hDualFour
  constructor
  · intro x
    have hxUpper := hHFour x
    by_contra hNot
    have hDegree : degree H x = 4 := by omega
    exact sevenRows_degreeFour_impossible hHClutter hHCard hHRows hBRows
      hBCard hBFour hDegree
  · exact hBFour

end AiMathLab.P0054.MiddleSevenNineDegree
