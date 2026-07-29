import AiMathLab.P0054AdjacentSixLift

/-!
# The arbitrary-finite adjacent six-row theorem

For six rows of size at least two and blocker rows of size at least four, the
blocker has at least six rows.  High point degree creates a forbidden small
transversal; degree three reduces to a three-row residual, and degree at most
two is discharged by the checked support-multigraph certificate.
-/

namespace AiMathLab.P0054.AdjacentSix

open AiMathLab.P0054.G413

theorem sixRow_maxDegreeAtMost_three_two_four {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4) :
    MaxDegreeAtMost H 3 := by
  classical
  intro x
  by_contra hDegree
  have hDegreeLower : 4 ≤ degree H x := by omega
  have hAvoidUpper : (avoidPoint H x).card ≤ 2 := by
    have hPartition := card_avoidPoint_add_degree H x
    omega
  interval_cases hAvoidCard : (avoidPoint H x).card
  · have hTransversal : IsTransversal H {x} := by
      intro E hEH
      have hxE : x ∈ E := by
        by_contra hxE
        have hEAvoid : E ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hEH, hxE⟩
        have hPositive : 0 < (avoidPoint H x).card :=
          Finset.card_pos.mpr ⟨E, hEAvoid⟩
        omega
      exact ⟨x, by simp, hxE⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  · obtain ⟨E, hAvoid⟩ := Finset.card_eq_one.mp hAvoidCard
    have hEAvoid : E ∈ avoidPoint H x := by simp [hAvoid]
    have hEH : E ∈ H := (mem_avoidPoint.mp hEAvoid).1
    obtain ⟨y, hyE⟩ : E.Nonempty := Finset.card_pos.mp (by
      have := hHRows E hEH
      omega)
    have hTransversal : IsTransversal H {x, y} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAE : A = E := by simpa [hAvoid] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      (Finset.card_le_two.trans_lt (by omega))
  · obtain ⟨P, Q, hPQ, hAvoid⟩ := Finset.card_eq_two.mp hAvoidCard
    have hPAvoid : P ∈ avoidPoint H x := by simp [hAvoid]
    have hQAvoid : Q ∈ avoidPoint H x := by simp [hAvoid]
    have hPH : P ∈ H := (mem_avoidPoint.mp hPAvoid).1
    have hQH : Q ∈ H := (mem_avoidPoint.mp hQAvoid).1
    obtain ⟨p, hpP⟩ : P.Nonempty := Finset.card_pos.mp (by
      have := hHRows P hPH
      omega)
    obtain ⟨q, hqQ⟩ : Q.Nonempty := Finset.card_pos.mp (by
      have := hHRows Q hQH
      omega)
    have hTransversal : IsTransversal H {x, p, q} := by
      intro A hAH
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint H x := mem_avoidPoint.mpr ⟨hAH, hxA⟩
        have hAPQ : A = P ∨ A = Q := by simpa [hAvoid] using hAAvoid
        rcases hAPQ with rfl | rfl
        · exact ⟨p, by simp, hpP⟩
        · exact ⟨q, by simp, hqQ⟩
    exact false_of_small_transversal hBRows hTransversal
      (Finset.card_le_three.trans_lt (by omega))

theorem blocker_card_ge_six_of_card_eq_six {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 2)
    (hBRows : RowsCardAtLeast (blocker H) 4) :
    6 ≤ (blocker H).card := by
  classical
  have hAtMostThree := sixRow_maxDegreeAtMost_three_two_four
    hHCard hHRows hBRows
  by_cases hAtMostTwo : MaxDegreeAtMost H 2
  · exact sixRow_lowDegree_blocker_card_ge_six_two_core
      hHCard hHRows hBRows hAtMostTwo
  · unfold MaxDegreeAtMost at hAtMostTwo
    push Not at hAtMostTwo
    obtain ⟨x, hx⟩ := hAtMostTwo
    have hDegree : degree H x = 3 := by
      have := hAtMostThree x
      omega
    let K := avoidPoint H x
    have hKCard : K.card = 3 := by
      have hPartition := card_avoidPoint_add_degree H x
      simpa [K, hHCard, hDegree] using hPartition
    have hKRows : RowsCardAtLeast K 2 := by
      intro E hE
      exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hE)).1
    have hBKRows : RowsCardAtLeast (blocker K) 3 := by
      rw [show blocker K = residual (blocker H) x by
        simpa [K] using blocker_avoidPoint hHClutter x]
      simpa using residual_rows_cardAtLeast hBRows x
    have hEight : 8 ≤ (blocker K).card :=
      threeRow_blocker_card_ge_eight_of_rows_cardAtLeast_three
        hKCard hKRows hBKRows
    have hLift : (blocker K).card ≤ (blocker H).card := by
      rw [show blocker K = residual (blocker H) x by
        simpa [K] using blocker_avoidPoint hHClutter x]
      exact residual_card_le (blocker H) x
    omega

end AiMathLab.P0054.AdjacentSix
