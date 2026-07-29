import AiMathLab.P0054G420.MiddleThreeRow
import AiMathLab.P0054G420.DegreeBounds

/-!
# Basic reductions for the middle split seven plus eight

The two blocker sides have minimum row size three.  Before the finite kernel
certificates are used, elementary residual arguments force maximum degrees
three and guarantee a three-point row on one of the two sides.
-/

namespace AiMathLab.P0054.MiddleSevenEightBasics

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420

theorem sevenRows_maxDegreeAtMost_five {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    MaxDegreeAtMost H 5 := by
  classical
  intro x
  by_contra hNot
  have hAvoidUpper : (avoidPoint H x).card ≤ 1 := by
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
    have hEPositive : 0 < E.card := by
      have := hHRows E hEH
      omega
    obtain ⟨y, hyE⟩ := Finset.card_pos.mp hEPositive
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x :=
          mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoidEq] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      ((Finset.card_le_two : ({x, y} : G413.Row α).card ≤ 2).trans_lt
        (by omega))

theorem eightRows_maxDegreeAtMost_four {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7) :
    MaxDegreeAtMost H 4 := by
  classical
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHRows
  have hDualMax : MaxDegreeAtMost (blocker H) 5 :=
    sevenRows_maxDegreeAtMost_five hBCard hBRows hDualRows
  intro x
  by_contra hNot
  have hAvoidUpper : (avoidPoint H x).card ≤ 3 := by
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
    have hEPositive : 0 < E.card := by
      have := hHRows E hEH
      omega
    obtain ⟨y, hyE⟩ := Finset.card_pos.mp hEPositive
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x :=
          mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoidEq] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      ((Finset.card_le_two : ({x, y} : G413.Row α).card ≤ 2).trans_lt
        (by omega))
  · have hNine : 9 ≤ degree (blocker H) x :=
      AiMathLab.P0054.G415.twoAvoidingRows_blockers_containing_card_ge_nine
        hHRows hBRows hAvoidCard
    have hUpper : degree (blocker H) x ≤ (blocker H).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · let K := avoidPoint H x
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
        _ ≤ 5 := hDualMax x
    have hBlockerUpper : (blocker K).card ≤ 8 := by
      have hLift := blocker_avoidPoint_card_le_blocker H x
      have : (blocker K).card ≤ 7 := by simpa [K, hBCard] using hLift
      omega
    exact threeRows_pair_five_total_eight_impossible hKClutter
      (by simpa [K] using hAvoidCard) hKRows hBKRows hPairUpper
        hBlockerUpper

theorem sevenRows_maxDegreeAtMost_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) :
    MaxDegreeAtMost H 3 := by
  classical
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHRows
  have hDualMax : MaxDegreeAtMost (blocker H) 4 :=
    eightRows_maxDegreeAtMost_four (blocker_isClutter H) hBCard hBRows
      hDualRows (by simpa [blocker_involution hHClutter] using hHCard)
  intro x
  by_contra hNot
  have hAvoidUpper : (avoidPoint H x).card ≤ 3 := by
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
    have hEPositive : 0 < E.card := by
      have := hHRows E hEH
      omega
    obtain ⟨y, hyE⟩ := Finset.card_pos.mp hEPositive
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x :=
          mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoidEq] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      ((Finset.card_le_two : ({x, y} : G413.Row α).card ≤ 2).trans_lt
        (by omega))
  · have hNine : 9 ≤ degree (blocker H) x :=
      AiMathLab.P0054.G415.twoAvoidingRows_blockers_containing_card_ge_nine
        hHRows hBRows hAvoidCard
    have hUpper : degree (blocker H) x ≤ (blocker H).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · let K := avoidPoint H x
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
        _ ≤ 4 := hDualMax x
        _ ≤ 5 := by omega
    have hBlockerUpper : (blocker K).card ≤ 8 := by
      simpa [K, hBCard] using blocker_avoidPoint_card_le_blocker H x
    exact threeRows_pair_five_total_eight_impossible hKClutter
      (by simpa [K] using hAvoidCard) hKRows hBKRows hPairUpper
        hBlockerUpper

theorem sevenEight_has_three_row {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHCard : H.card = 7)
    (hBCard : (blocker H).card = 8)
    (hRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    (∃ D ∈ H, D.card = 3) ∨
      ∃ E ∈ blocker H, E.card = 3 := by
  classical
  by_contra hNoThree
  push Not at hNoThree
  have hRowsFour : RowsCardAtLeast H 4 := by
    intro D hDH
    have := hRows D hDH
    have hne := hNoThree.1 D hDH
    omega
  have hBRowsFour : RowsCardAtLeast (blocker H) 4 := by
    intro E hEH
    have := hBRows E hEH
    have hne := hNoThree.2 E hEH
    omega
  obtain ⟨D, hDH⟩ : H.Nonempty := Finset.card_pos.mp (by omega)
  let indices := middleIndexSet H
  have hIndexCard : indices.card = 15 := by
    simpa [indices, middleIndexSet, hHCard, hBCard]
  have hEventBound : ∀ i ∈ indices,
      (middleEvent i).card ≤ 2 ^ (Fintype.card α - 4) := by
    intro i hi
    apply middleEvent_card_le
    · intro A hiA
      subst i
      exact hRowsFour A (by simpa [indices, middleIndexSet] using hi)
    · intro A hiA
      subst i
      exact hBRowsFour A (by simpa [indices, middleIndexSet] using hi)
  have hGroundFour : 4 ≤ Fintype.card α :=
    (hRowsFour D hDH).trans (Finset.card_le_univ D)
  have hPower :
      2 ^ Fintype.card α = 16 * 2 ^ (Fintype.card α - 4) := by
    calc
      2 ^ Fintype.card α = 2 ^ (4 + (Fintype.card α - 4)) := by
        rw [Nat.add_sub_of_le hGroundFour]
      _ = 16 * 2 ^ (Fintype.card α - 4) := by norm_num [pow_add]
  have hCoverCard :
      2 ^ Fintype.card α ≤ (indices.biUnion middleEvent).card := by
    calc
      2 ^ Fintype.card α =
          (Finset.univ.powerset : Finset (G413.Row α)).card := by simp
      _ ≤ (indices.biUnion middleEvent).card :=
        Finset.card_le_card (by
          simpa [indices] using middleEvents_cover H)
  have hUnionUpper : (indices.biUnion middleEvent).card ≤
      ∑ i ∈ indices, (middleEvent i).card := Finset.card_biUnion_le
  have hSumUpper : (∑ i ∈ indices, (middleEvent i).card) ≤
      15 * 2 ^ (Fintype.card α - 4) := by
    calc
      (∑ i ∈ indices, (middleEvent i).card) ≤
          indices.card * 2 ^ (Fintype.card α - 4) :=
        Finset.sum_le_card_nsmul indices _ _ hEventBound
      _ = 15 * 2 ^ (Fintype.card α - 4) := by rw [hIndexCard]
  have hPositive : 0 < 2 ^ (Fintype.card α - 4) :=
    pow_pos (by decide : 0 < (2 : Nat)) _
  rw [hPower] at hCoverCard
  omega

end AiMathLab.P0054.MiddleSevenEightBasics
