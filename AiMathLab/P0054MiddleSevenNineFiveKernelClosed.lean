import AiMathLab.P0054MiddleSevenNineBridge
import AiMathLab.P0054G420.FiveRowPairExactPrinciple

/-!
# Closing the five-row rank-three principle

The five-row branch can be closed without a separate five-row multiplicity
classification.  A degree-three point leaves two avoiding rows.  Their
intersection has size at most three because every common point gives a
distinct pair blocker.  The two-row blocker count and the lift inequality
exclude intersection sizes zero, one, and two.  In the remaining size-three
case the residual blocker has exactly three rows; the three-row product bound
then contradicts the fact that a residual of a five-row family has at most
five rows.
-/

namespace AiMathLab.P0054.MiddleSevenNineFiveKernelClosed

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineBridge

theorem fiveRowRowsFourImpossiblePrinciple
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha] :
    FiveRowRowsFourImpossiblePrinciple alpha := by
  classical
  intro K hKClutter hKCard hKRows _hKUpper hBKRows hKMax hBKUpper
    hPairUpper
  have hKRowsThree : RowsCardAtLeast K 3 := by
    intro R hRK
    have hLower := hKRows R hRK
    omega
  have hNotLow : ¬MaxDegreeAtMost K 2 := by
    intro hLow
    have hFifteen :=
      AiMathLab.P0054.G416.fiveRow_lowDegree_blocker_card_ge_fifteen
        hKCard hKRowsThree hLow
    omega
  unfold MaxDegreeAtMost at hNotLow
  push Not at hNotLow
  obtain ⟨x, hxLower⟩ := hNotLow
  have hxDegree : degree K x = 3 := by
    have hxUpper := hKMax x
    omega
  have hAvoidCard : (avoidPoint K x).card = 2 := by
    have hPartition := card_avoidPoint_add_degree K x
    omega
  obtain ⟨P, Q, hPQ, hAvoid⟩ := Finset.card_eq_two.mp hAvoidCard
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hQAvoid : Q ∈ avoidPoint K x := by simp [hAvoid]
  have hPK : P ∈ K := (mem_avoidPoint.mp hPAvoid).1
  have hQK : Q ∈ K := (mem_avoidPoint.mp hQAvoid).1
  have hxP : x ∉ P := (mem_avoidPoint.mp hPAvoid).2
  have hPCard : 4 ≤ P.card := hKRows P hPK
  have hQCard : 4 ≤ Q.card := hKRows Q hQK
  have hCommonUpper : (P ∩ Q).card ≤ 3 := by
    exact (commonPairRows_card_le hKCard hKMax hAvoid).trans hPairUpper
  have hPParts := Finset.card_sdiff_add_card_inter P Q
  have hQParts := Finset.card_sdiff_add_card_inter Q P
  rw [Finset.inter_comm Q P] at hQParts
  have hSourceBound :
      (P ∩ Q).card + (P \ Q).card * (Q \ P).card ≤
        (blocker (avoidPoint K x)).card := by
    rw [hAvoid]
    exact twoRow_blocker_card_ge_inter_add_sdiff_product P Q
  have hLiftBound :=
    twoAvoidingRows_source_add_common_le_degree_add_pairs
      hKCard hKMax hAvoid
  let R := residual K x
  let B := avoidPoint (blocker K) x
  have hRClutter : IsClutter R := by
    simpa [R] using residual_isClutter K x
  have hRRows : RowsCardAtLeast R 3 := by
    simpa [R] using residual_rows_cardAtLeast hKRows x
  have hBlockerR : blocker R = B := by
    simpa [R, B] using blocker_residual K x
  have hBlockerB : blocker B = R := by
    rw [← hBlockerR, blocker_involution hRClutter]
  have hBRows : RowsCardAtLeast B 2 := by
    intro row hRow
    exact hBKRows row (mem_avoidPoint.mp (by simpa [B] using hRow)).1
  have hBLower : 3 ≤ B.card := by
    by_contra hNot
    have hBUpperTwo : B.card ≤ 2 := by omega
    have hPDelete : P ∈ deletePoint K x :=
      Finset.mem_image.mpr ⟨P, hPK, by simp [hxP]⟩
    obtain ⟨M, hMR, -⟩ := exists_minimize_subset hPDelete
    have hMR' : M ∈ R := by
      change M ∈ minimize (deletePoint K x)
      exact hMR
    have hMBlocker : M ∈ blocker B := by
      rw [hBlockerB]
      exact hMR'
    have hMUpper :=
      minimalTransversal_card_le_rows (mem_blocker.mp hMBlocker)
    have hMLower := hRRows M hMR'
    omega
  have hBlockerPartition := card_avoidPoint_add_degree (blocker K) x
  interval_cases hCommonCard : (P ∩ Q).card
  · have hPDiff : 4 ≤ (P \ Q).card := by omega
    have hQDiff : 4 ≤ (Q \ P).card := by omega
    have hProduct : 16 ≤ (P \ Q).card * (Q \ P).card := by
      calc
        16 = 4 * 4 := rfl
        _ ≤ (P \ Q).card * (Q \ P).card :=
          Nat.mul_le_mul hPDiff hQDiff
    change 3 ≤ (avoidPoint (blocker K) x).card at hBLower
    omega
  · have hPDiff : 3 ≤ (P \ Q).card := by omega
    have hQDiff : 3 ≤ (Q \ P).card := by omega
    have hProduct : 9 ≤ (P \ Q).card * (Q \ P).card := by
      calc
        9 = 3 * 3 := rfl
        _ ≤ (P \ Q).card * (Q \ P).card :=
          Nat.mul_le_mul hPDiff hQDiff
    change 3 ≤ (avoidPoint (blocker K) x).card at hBLower
    omega
  · have hPDiff : 2 ≤ (P \ Q).card := by omega
    have hQDiff : 2 ≤ (Q \ P).card := by omega
    have hProduct : 4 ≤ (P \ Q).card * (Q \ P).card := by
      calc
        4 = 2 * 2 := rfl
        _ ≤ (P \ Q).card * (Q \ P).card :=
          Nat.mul_le_mul hPDiff hQDiff
    change 3 ≤ (avoidPoint (blocker K) x).card at hBLower
    omega
  · have hPDiff : 1 ≤ (P \ Q).card := by omega
    have hQDiff : 1 ≤ (Q \ P).card := by omega
    have hProduct : 1 ≤ (P \ Q).card * (Q \ P).card := by
      calc
        1 = 1 * 1 := rfl
        _ ≤ (P \ Q).card * (Q \ P).card :=
          Nat.mul_le_mul hPDiff hQDiff
    have hBCard : B.card = 3 := by
      change (avoidPoint (blocker K) x).card = 3
      change 3 ≤ (avoidPoint (blocker K) x).card at hBLower
      omega
    have hBlockerBRows : RowsCardAtLeast (blocker B) 3 := by
      rw [hBlockerB]
      exact hRRows
    have hEight : 8 ≤ (blocker B).card :=
      threeRow_blocker_card_ge_eight_of_rows_cardAtLeast_three
        hBCard hBRows hBlockerBRows
    have hRUpper : R.card ≤ 5 := by
      have hRUpperK : R.card ≤ K.card := by
        simpa [R] using residual_card_le K x
      exact hRUpperK.trans_eq hKCard
    rw [hBlockerB] at hEight
    omega

end AiMathLab.P0054.MiddleSevenNineFiveKernelClosed
