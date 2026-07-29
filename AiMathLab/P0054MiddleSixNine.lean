import AiMathLab.P0054MiddleSixNineKernel

/-!
# Exclusion of the middle split six plus nine
-/

namespace AiMathLab.P0054.MiddleSixNine

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419

theorem sixNine_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 9) : False := by
  classical
  have hHNonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  have hDegreeUpper :=
    AiMathLab.P0054.MiddleLower.sixRow_maxDegreeAtMost_four
      hHCard hHRows hBRows
  by_cases hAtMostThree : MaxDegreeAtMost H 3
  · by_cases hLow : MaxDegreeAtMost H 2
    · have hFifteen := AiMathLab.P0054.G417.sixRow_lowDegree_blocker_card_ge_fifteen
        hHCard hHRows hLow
      omega
    · unfold MaxDegreeAtMost at hLow
      push Not at hLow
      obtain ⟨x, hx⟩ := hLow
      have hDegree : degree H x = 3 := by
        have := hAtMostThree x
        omega
      let K := avoidPoint H x
      have hPairToDegree :
          (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        have h := pairRows_blocker_avoidPoint_card_le_degree hBRows x
        simpa [K] using h
      have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
        rw [blocker_involution hHClutter]
        exact hHRows
      have hDualCard : (blocker (blocker H)).card = 6 := by
        rw [blocker_involution hHClutter]
        exact hHCard
      have hBlockerDegrees : MaxDegreeAtMost (blocker H) 5 :=
        AiMathLab.P0054.MiddleNineDegree.nineRows_maxDegreeAtMost_five
          (blocker_isClutter H) hBCard hBRows hDualRows hDualCard
      have hPairUpper : (pairRows (blocker K)).card ≤ 5 :=
        hPairToDegree.trans (hBlockerDegrees x)
      have hKernelUpper : (blocker K).card ≤ 9 := by
        have h := blocker_avoidPoint_card_le_blocker H x
        simpa [K, hBCard] using h
      obtain ⟨A, B, C, hAB, hAC, hBC, hKForm, hProfile⟩ :=
        AiMathLab.P0054.MiddleSixProfile.degreeThree_kernel_profile
          hHClutter hHCard hHRows hBRows hDegree
          (by simpa [K] using hPairUpper.trans (by omega))
          (hKernelUpper.trans (by omega))
      unfold OrderedThreeKernelProfile at hProfile
      rcases hProfile with hProfile | hProfile | hProfile | hProfile |
        hProfile | hProfile | hProfile
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hSix : 6 ≤ (pairRows (blocker K)).card := by
          have h := threePairGenerated_card_le_pairRows hKForm
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using h
        omega
      · exact AiMathLab.P0054.MiddleSixNineKernel.kernelB_impossible
          hHClutter hHCard hHRows hBRows hBCard hDegree
          hKForm hAB hAC hBC (by
            unfold IsKernelBProfile
            exact Or.inl hProfile)
      · exact AiMathLab.P0054.MiddleSixNineKernel.kernelB_impossible
          hHClutter hHCard hHRows hBRows hBCard hDegree
          hKForm hAB hAC hBC (by
            unfold IsKernelBProfile
            exact Or.inr (Or.inl hProfile))
      · exact AiMathLab.P0054.MiddleSixNineKernel.kernelB_impossible
          hHClutter hHCard hHRows hBRows hBCard hDegree
          hKForm hAB hAC hBC (by
            unfold IsKernelBProfile
            exact Or.inr (Or.inr hProfile))
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hSix : 6 ≤ (pairRows (blocker K)).card := by
          have h := threePairGenerated_card_le_pairRows hKForm
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using h
        omega
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hSix : 6 ≤ (pairRows (blocker K)).card := by
          have h := threePairGenerated_card_le_pairRows hKForm
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using h
        omega
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hSix : 6 ≤ (pairRows (blocker K)).card := by
          have h := threePairGenerated_card_le_pairRows hKForm
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using h
        omega
  · unfold MaxDegreeAtMost at hAtMostThree
    push Not at hAtMostThree
    obtain ⟨x, hx⟩ := hAtMostThree
    have hDegree : degree H x = 4 := by
      have := hDegreeUpper x
      omega
    have hContaining : 9 ≤ degree (blocker H) x :=
      AiMathLab.P0054.G418.degreeFour_blockers_containing_card_ge_nine
        hHCard hHRows hBRows hDegree
    have hAvoiding : 2 ≤ (avoidPoint (blocker H) x).card :=
      AiMathLab.P0054.MiddleLower.avoid_blocker_card_ge_two
        hHNonempty hHRows x
    have hPartition := card_avoidPoint_add_degree (blocker H) x
    omega

end AiMathLab.P0054.MiddleSixNine
