import AiMathLab.P0054G420.FiveRowPairExactOneCommon

namespace AiMathLab.P0054.G420

open G413 G419

theorem fiveRowPairExactPrinciple (alpha : Type*)
    [Fintype alpha] [DecidableEq alpha] :
    FiveRowPairExactPrinciple alpha := by
  classical
  intro K hKClutter hKCard hKRows hMaxDegree hBlockerUpper hPairUpper
  by_contra hNotExact
  have hPairAtMostTwo : (pairRows (blocker K)).card ≤ 2 := by omega
  have hNotLowDegree : ¬MaxDegreeAtMost K 2 := by
    intro hLowDegree
    have hFifteen := G416.fiveRow_lowDegree_blocker_card_ge_fifteen
      hKCard hKRows hLowDegree
    omega
  unfold MaxDegreeAtMost at hNotLowDegree
  push Not at hNotLowDegree
  obtain ⟨x, hxDegreeLower⟩ := hNotLowDegree
  have hxDegree : degree K x = 3 := by
    have hxDegreeUpper := hMaxDegree x
    omega
  have hAvoidCard : (avoidPoint K x).card = 2 := by
    have hPartition := card_avoidPoint_add_degree K x
    omega
  obtain ⟨P, Q, hPQ, hAvoid⟩ := Finset.card_eq_two.mp hAvoidCard
  have hPAvoid : P ∈ avoidPoint K x := by simp [hAvoid]
  have hQAvoid : Q ∈ avoidPoint K x := by simp [hAvoid]
  have hPK : P ∈ K := (mem_avoidPoint.mp hPAvoid).1
  have hQK : Q ∈ K := (mem_avoidPoint.mp hQAvoid).1
  have hPCard : 3 ≤ P.card := hKRows P hPK
  have hQCard : 3 ≤ Q.card := hKRows Q hQK
  have hCommonUpper : (P ∩ Q).card ≤ 2 := by
    exact (commonPairRows_card_le hKCard hMaxDegree hAvoid).trans hPairAtMostTwo
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
      hKCard hMaxDegree hAvoid
  have hBlockerPartition := card_avoidPoint_add_degree (blocker K) x
  interval_cases hCommonCard : (P ∩ Q).card
  · have hPDiff : 3 ≤ (P \ Q).card := by omega
    have hQDiff : 3 ≤ (Q \ P).card := by omega
    have hProduct : 9 ≤ (P \ Q).card * (Q \ P).card := by
      have := Nat.mul_le_mul hPDiff hQDiff
      norm_num at this ⊢
      exact this
    have hSource : 9 ≤ (blocker (avoidPoint K x)).card := by omega
    have hBlockerDegree : 7 ≤ degree (blocker K) x := by omega
    have hAvoidBlocker : 2 ≤ (avoidPoint (blocker K) x).card :=
      avoidBlocker_card_ge_two_of_two_avoidingRows hKRows hAvoid
    omega
  · have hPDiff : 2 ≤ (P \ Q).card := by omega
    have hQDiff : 2 ≤ (Q \ P).card := by omega
    have hProduct : 4 ≤ (P \ Q).card * (Q \ P).card := by
      have := Nat.mul_le_mul hPDiff hQDiff
      norm_num at this ⊢
      exact this
    have hSource : 5 ≤ (blocker (avoidPoint K x)).card := by omega
    have hBlockerDegree : 4 ≤ degree (blocker K) x := by omega
    have hAvoidBlocker : 5 ≤ (avoidPoint (blocker K) x).card :=
      avoidBlocker_card_ge_five_of_one_commonPoint
        hKCard hKRows hMaxDegree hPairAtMostTwo hAvoid hCommonCard
    omega
  · have hPDiff : 1 ≤ (P \ Q).card := by omega
    have hQDiff : 1 ≤ (Q \ P).card := by omega
    have hProduct : 1 ≤ (P \ Q).card * (Q \ P).card := by
      have := Nat.mul_le_mul hPDiff hQDiff
      norm_num at this ⊢
      exact this
    have hSource : 3 ≤ (blocker (avoidPoint K x)).card := by omega
    have hBlockerDegree : 3 ≤ degree (blocker K) x := by omega
    have hAvoidBlocker : 6 ≤ (avoidPoint (blocker K) x).card :=
      avoidBlocker_card_ge_six_of_two_commonPoints
        hKCard hKRows hMaxDegree hxDegree hPairAtMostTwo hAvoid hCommonCard
    omega

end AiMathLab.P0054.G420
