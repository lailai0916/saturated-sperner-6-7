import AiMathLab.P0054MiddleSixProfile

/-!
# Exclusion of the middle split six plus eight
-/

namespace AiMathLab.P0054.MiddleSixEight

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419

theorem sixEight_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) : False := by
  classical
  have hHNonempty : H.Nonempty := Finset.card_pos.mp (by omega)
  have hDegreeUpper := MiddleLower.sixRow_maxDegreeAtMost_four
    hHCard hHRows hBRows
  by_cases hAtMostThree : MaxDegreeAtMost H 3
  · by_cases hLow : MaxDegreeAtMost H 2
    · have hFifteen := G417.sixRow_lowDegree_blocker_card_ge_fifteen
        hHCard hHRows hLow
      omega
    · unfold MaxDegreeAtMost at hLow
      push Not at hLow
      obtain ⟨x, hx⟩ := hLow
      have hDegree : degree H x = 3 := by
        have := hAtMostThree x
        omega
      let K := avoidPoint H x
      have hKCard : K.card = 3 := by
        have hPartition := card_avoidPoint_add_degree H x
        simpa [K, hHCard, hDegree] using hPartition
      have hKClutter : IsClutter K := by
        simpa [K] using avoidPoint_isClutter hHClutter x
      have hKRows : RowsCardAtLeast K 3 := by
        intro E hE
        exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hE)).1
      have hBKRows : RowsCardAtLeast (blocker K) 2 := by
        simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
      have hAvoidLower : 2 ≤ (avoidPoint (blocker H) x).card :=
        MiddleLower.avoid_blocker_card_ge_two hHNonempty hHRows x
      have hDegreeBUpper : degree (blocker H) x ≤ 6 := by
        have hPartition := card_avoidPoint_add_degree (blocker H) x
        omega
      have hPairToDegree :
          (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        have h := pairRows_blocker_avoidPoint_card_le_degree hBRows x
        simpa [K] using h
      have hPairUpper : (pairRows (blocker K)).card ≤ 6 :=
        hPairToDegree.trans hDegreeBUpper
      have hKernelUpper : (blocker K).card ≤ 8 := by
        have h := blocker_avoidPoint_card_le_blocker H x
        simpa [K, hBCard] using h
      obtain ⟨A, B, C, hAB, hAC, hBC, hKForm, hProfile⟩ :=
        MiddleSixProfile.degreeThree_kernel_profile
          hHClutter hHCard hHRows hBRows hDegree
          (by simpa [K] using hPairUpper)
          (hKernelUpper.trans (by omega))
      have hGenerated := threeGeneratedRows_card_le_blocker
        hKForm hAB hAC hBC
      unfold OrderedThreeKernelProfile at hProfile
      rcases hProfile with hProfile | hProfile | hProfile | hProfile |
        hProfile | hProfile | hProfile
      · rcases hProfile with ⟨hPA, hPB, hPC, hX, hY, hZ⟩
        have hPairLower : 6 ≤ (pairRows (blocker K)).card := by
          have h := threePairGenerated_card_le_pairRows hKForm
          simpa [K, hPA, hPB, hPC, hX, hY, hZ] using h
        have hPairCard : (pairRows (blocker K)).card = 6 := by omega
        have hTripleCard : (rowsCardExactly (blocker K) 3).card = 1 := by
          rw [threeRow_triple_blockers_card hKForm hAB hAC hBC]
          simp [hPA, hPB, hPC]
        have hBKCard : (blocker K).card = 7 := by
          have hAdd := threeRow_blocker_card_add_pair_triple hKCard hBKRows
          omega
        let liftedPairs :=
          (pairRows (blocker K)).image (avoidBlockerLift H x)
        have hLiftedCard : liftedPairs.card = 6 := by
          calc
            liftedPairs.card = (pairRows (blocker K)).card := by
              apply Finset.card_image_iff.mpr
              intro T hT U hU hEq
              exact avoidBlockerLift_injective H x
                (Finset.mem_filter.mp hT).1
                (Finset.mem_filter.mp hU).1 hEq
            _ = 6 := hPairCard
        have hLiftedSubset :
            liftedPairs ⊆ (blocker H).filter fun E ↦ x ∈ E := by
          intro T hT
          obtain ⟨U, hUPair, rfl⟩ := Finset.mem_image.mp hT
          obtain ⟨hUBlocker, hUCard⟩ := Finset.mem_filter.mp hUPair
          refine Finset.mem_filter.mpr
            ⟨avoidBlockerLift_mem_blocker hUBlocker, ?_⟩
          unfold avoidBlockerLift
          split
          · rename_i hTransversal
            exact (false_of_small_transversal hBRows hTransversal
              (by omega)).elim
          · simp
        have hDegreeBLower : 6 ≤ degree (blocker H) x := by
          have h := Finset.card_le_card hLiftedSubset
          simpa [degree, hLiftedCard] using h
        have hDegreeB : degree (blocker H) x = 6 := by omega
        have hAvoidCard : (avoidPoint (blocker H) x).card = 2 := by
          have hPartition := card_avoidPoint_add_degree (blocker H) x
          omega
        have hContainingCard :
            ((blocker H).filter fun E ↦ x ∈ E).card = 6 := by
          simpa [degree] using hDegreeB
        have hLiftedEq :
            liftedPairs = (blocker H).filter fun E ↦ x ∈ E :=
          Finset.eq_of_subset_of_card_le hLiftedSubset (by
            rw [hLiftedCard, hContainingCard])
        obtain ⟨T, hTripleFamily⟩ := Finset.card_eq_one.mp hTripleCard
        have hTTriple : T ∈ rowsCardExactly (blocker K) 3 := by
          simp [hTripleFamily]
        obtain ⟨hTK, hTCard⟩ := mem_rowsCardExactly.mp hTTriple
        have hxT : x ∉ T := blocker_rows_avoid_inactive
          (fun E hE ↦ (mem_avoidPoint.mp
            (by simpa [K] using hE)).2) T hTK
        have hLiftMember : avoidBlockerLift H x T ∈ blocker H :=
          avoidBlockerLift_mem_blocker hTK
        have hLiftAvoid : x ∉ avoidBlockerLift H x T := by
          intro hxLift
          have hLiftContaining :
              avoidBlockerLift H x T ∈
                (blocker H).filter fun E ↦ x ∈ E :=
            Finset.mem_filter.mpr ⟨hLiftMember, hxLift⟩
          have hLiftImage : avoidBlockerLift H x T ∈ liftedPairs := by
            rw [hLiftedEq]
            exact hLiftContaining
          obtain ⟨U, hUPair, hULift⟩ := Finset.mem_image.mp hLiftImage
          obtain ⟨hUK, hUCard⟩ := Finset.mem_filter.mp hUPair
          have hUT : U = T :=
            avoidBlockerLift_injective H x hUK hTK hULift
          rw [hUT] at hUCard
          omega
        have hTAvoid : T ∈ avoidPoint (blocker H) x := by
          by_cases hTransversal : IsTransversal H T
          · have hTH : T ∈ blocker H := by
              simpa [avoidBlockerLift, hTransversal] using hLiftMember
            exact mem_avoidPoint.mpr ⟨hTH, hxT⟩
          · have hxLift : x ∈ avoidBlockerLift H x T := by
              simp [avoidBlockerLift, hTransversal]
            exact (hLiftAvoid hxLift).elim
        obtain ⟨E₀, E₁, hE₀E₁, hAvoidForm⟩ :=
          Finset.card_eq_two.mp hAvoidCard
        have hE₀Avoid : E₀ ∈ avoidPoint (blocker H) x := by
          simp [hAvoidForm]
        have hE₁Avoid : E₁ ∈ avoidPoint (blocker H) x := by
          simp [hAvoidForm]
        have hE₀B : E₀ ∈ blocker H := (mem_avoidPoint.mp hE₀Avoid).1
        have hE₁B : E₁ ∈ blocker H := (mem_avoidPoint.mp hE₁Avoid).1
        have hE₀Card : 3 ≤ E₀.card := hBRows E₀ hE₀B
        have hE₁Card : 3 ≤ E₁.card := hBRows E₁ hE₁B
        let R := residual H x
        have hRClutter : IsClutter R := by
          simpa [R] using residual_isClutter H x
        have hRRows : RowsCardAtLeast R 2 := by
          simpa [R] using residual_rows_cardAtLeast hHRows x
        have hBlockerR : blocker R = {E₀, E₁} := by
          calc
            blocker R = avoidPoint (blocker H) x := by
              simpa [R] using blocker_residual H x
            _ = {E₀, E₁} := hAvoidForm
        have hPairBlocker :
            blocker ({E₀, E₁} : G413.Hypergraph α) = R := by
          calc
            blocker ({E₀, E₁} : G413.Hypergraph α) =
                blocker (blocker R) := congrArg blocker hBlockerR.symm
            _ = R := blocker_involution hRClutter
        by_cases hInter : (E₀ ∩ E₁).Nonempty
        · obtain ⟨z, hz⟩ := hInter
          have hz₀ : z ∈ E₀ := (Finset.mem_inter.mp hz).1
          have hz₁ : z ∈ E₁ := (Finset.mem_inter.mp hz).2
          have hSingletonTransversal :
              IsTransversal ({E₀, E₁} : G413.Hypergraph α) {z} := by
            intro E hE
            simp only [Finset.mem_insert, Finset.mem_singleton] at hE
            rcases hE with rfl | rfl
            · exact ⟨z, by simp, hz₀⟩
            · exact ⟨z, by simp, hz₁⟩
          have hSingleton :
              {z} ∈ blocker ({E₀, E₁} : G413.Hypergraph α) := by
            apply mem_blocker.mpr
            apply hSingletonTransversal.minimal_of_privateRows
            intro y hy
            have hyz : y = z := by simpa using hy
            subst y
            exact ⟨E₀, by simp, by simp, hz₀, by
              intro w hw hw₀
              simpa using hw⟩
          rw [hPairBlocker] at hSingleton
          have hRowLower := hRRows {z} hSingleton
          simp at hRowLower
        · have hDisjoint : Disjoint E₀ E₁ := by
            rw [Finset.disjoint_iff_inter_eq_empty]
            exact Finset.not_nonempty_iff_eq_empty.mp hInter
          have hProduct : E₀.card * E₁.card ≤ R.card := by
            rw [← hPairBlocker]
            exact twoRow_blocker_card_ge_product (by
              rw [hPairBlocker]
              exact hRRows)
          have hRUpper : R.card ≤ 6 := by
            exact (residual_card_le H x).trans_eq hHCard
          have : 9 ≤ E₀.card * E₁.card := by
            norm_num
            exact Nat.mul_le_mul hE₀Card hE₁Card
          omega
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hNine : 9 ≤ (blocker K).card := by
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using hGenerated
        omega
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hNine : 9 ≤ (blocker K).card := by
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using hGenerated
        omega
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hNine : 9 ≤ (blocker K).card := by
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using hGenerated
        omega
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hNine : 9 ≤ (blocker K).card := by
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using hGenerated
        omega
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hNine : 9 ≤ (blocker K).card := by
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using hGenerated
        omega
      · rcases hProfile with ⟨hp, hq, hr, hx12, hx13, hx23⟩
        have hNine : 9 ≤ (blocker K).card := by
          simpa [K, hp, hq, hr, hx12, hx13, hx23] using hGenerated
        omega
  · unfold MaxDegreeAtMost at hAtMostThree
    push Not at hAtMostThree
    obtain ⟨x, hx⟩ := hAtMostThree
    have hDegree : degree H x = 4 := by
      have := hDegreeUpper x
      omega
    have hNine := G418.degreeFour_blockers_containing_card_ge_nine
      hHCard hHRows hBRows hDegree
    have hUpper : degree (blocker H) x ≤ (blocker H).card :=
      Finset.card_filter_le _ _
    omega

end AiMathLab.P0054.MiddleSixEight
