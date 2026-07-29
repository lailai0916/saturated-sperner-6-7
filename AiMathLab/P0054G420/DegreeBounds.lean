import AiMathLab.P0054G419

namespace AiMathLab.P0054.G420

open G413

theorem eightRows_maxDegreeAtMost_five {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) :
    MaxDegreeAtMost H 5 := by
  classical
  intro x
  by_contra hDegreeUpper
  have hDegreeLower : 6 ≤ degree H x := by omega
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
        have hPositive : 0 < (avoidPoint H x).card :=
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
      ((Finset.card_le_two : ({x, y} : Row α).card ≤ 2).trans_lt (by omega))
  · have hNine : 9 ≤ degree (blocker H) x :=
      G415.twoAvoidingRows_blockers_containing_card_ge_nine
        hHRows hBRows hAvoidCard
    have hDegreeCard : degree (blocker H) x ≤ (blocker H).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega

theorem middle_maxDegreesAtMost_five {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) :
    MaxDegreeAtMost H 5 ∧ MaxDegreeAtMost (blocker H) 5 := by
  constructor
  · exact eightRows_maxDegreeAtMost_five hHCard hHRows hBRows hBCard
  · apply eightRows_maxDegreeAtMost_five hBCard hBRows
    · simpa [blocker_involution hHClutter] using hHRows
    · simpa [blocker_involution hHClutter] using hHCard

theorem tightBounds_contradict_orderedThreeKernelProfile
    {p q r x12 x13 x23 : Nat}
    (hProfile : G419.OrderedThreeKernelProfile p q r x12 x13 x23)
    (hPair :
      x12 * x13 + x12 * x23 + x13 * x23 +
        x12 * r + x13 * q + x23 * p ≤ 5)
    (hTotal :
      x12 * x13 + x12 * x23 + x13 * x23 +
        x12 * r + x13 * q + x23 * p + p * q * r ≤ 8) :
    False := by
  unfold G419.OrderedThreeKernelProfile at hProfile
  rcases hProfile with h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
      norm_num at hPair <;> norm_num at hTotal

theorem threeRows_pair_five_total_eight_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {K : G413.Hypergraph α}
    (hKClutter : IsClutter K)
    (hKCard : K.card = 3)
    (hKRows : RowsCardAtLeast K 3)
    (hBKRows : RowsCardAtLeast (blocker K) 2)
    (hPairUpper : (pairRows (blocker K)).card ≤ 5)
    (hBlockerUpper : (blocker K).card ≤ 8) :
    False := by
  classical
  obtain ⟨A, B, C, hAB, hAC, hBC, hK⟩ := Finset.card_eq_three.mp hKCard
  have hNoCommon : ∀ u, ¬(u ∈ A ∧ u ∈ B ∧ u ∈ C) :=
    no_common_point_of_threeRows_of_blocker_rows_cardAtLeast_two hK hBKRows
  have hAK : A ∈ K := by simp [hK]
  have hBK : B ∈ K := by simp [hK]
  have hCK : C ∈ K := by simp [hK]
  have hAnotB : ¬A ⊆ B := fun hSubset ↦ hAB (hKClutter hAK hBK hSubset)
  have hBnotA : ¬B ⊆ A := fun hSubset ↦ hAB (hKClutter hBK hAK hSubset).symm
  have hAnotC : ¬A ⊆ C := fun hSubset ↦ hAC (hKClutter hAK hCK hSubset)
  have hCnotA : ¬C ⊆ A := fun hSubset ↦ hAC (hKClutter hCK hAK hSubset).symm
  have hBnotC : ¬B ⊆ C := fun hSubset ↦ hBC (hKClutter hBK hCK hSubset)
  have hCnotB : ¬C ⊆ B := fun hSubset ↦ hBC (hKClutter hCK hBK hSubset).symm
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
  rw [G419.threePart_union_card hNoCommon] at hACard
  rw [G419.threePart_union_card_second hNoCommon] at hBCard
  rw [G419.threePart_union_card_third hNoCommon] at hCCard
  have hPair :
      (sharedPart A B C).card * (sharedPart A C B).card +
          (sharedPart A B C).card * (sharedPart B C A).card +
          (sharedPart A C B).card * (sharedPart B C A).card +
          (sharedPart A B C).card * (privatePart C A B).card +
          (sharedPart A C B).card * (privatePart B A C).card +
          (sharedPart B C A).card * (privatePart A B C).card ≤ 5 :=
    (G419.threePairGenerated_card_le_pairRows hK).trans hPairUpper
  have hTotal :
      (sharedPart A B C).card * (sharedPart A C B).card +
          (sharedPart A B C).card * (sharedPart B C A).card +
          (sharedPart A C B).card * (sharedPart B C A).card +
          (sharedPart A B C).card * (privatePart C A B).card +
          (sharedPart A C B).card * (privatePart B A C).card +
          (sharedPart B C A).card * (privatePart A B C).card +
          (privatePart A B C).card *
            (privatePart B A C).card *
            (privatePart C A B).card ≤ 8 :=
    (G419.threeGeneratedRows_card_le_blocker hK hAB hAC hBC).trans hBlockerUpper
  have hProfile := G419.orderedThreeKernelProfile_of_bounds
    (privatePart A B C).card
    (privatePart B A C).card
    (privatePart C A B).card
    (sharedPart A B C).card
    (sharedPart A C B).card
    (sharedPart B C A).card
    hACard hBCard hCCard hPY hQZ hPX hRZ hQX hRY
    (hPair.trans (by omega)) (hTotal.trans (by omega))
  exact tightBounds_contradict_orderedThreeKernelProfile hProfile hPair hTotal

theorem eightRows_degreeFive_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8)
    {x : α} (hDegree : degree H x = 5) :
    False := by
  let K := avoidPoint H x
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using G419.avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using G419.blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hDualDegree : MaxDegreeAtMost (blocker H) 5 :=
    (middle_maxDegreesAtMost_five hHClutter hHCard hHRows hBRows hBCard).2
  have hPairUpper : (pairRows (blocker K)).card ≤ 5 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using G419.pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 5 := hDualDegree x
  have hBlockerUpper : (blocker K).card ≤ 8 := by
    have hLift := G419.blocker_avoidPoint_card_le_blocker H x
    simpa [K, hBCard] using hLift
  exact threeRows_pair_five_total_eight_impossible
    hKClutter hKCard hKRows hBKRows hPairUpper hBlockerUpper

theorem middle_maxDegreesAtMost_four {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) :
    MaxDegreeAtMost H 4 ∧ MaxDegreeAtMost (blocker H) 4 := by
  have hDegreeFive := middle_maxDegreesAtMost_five
    hHClutter hHCard hHRows hBRows hBCard
  constructor
  · intro x
    have hUpper := hDegreeFive.1 x
    by_contra hnot
    have hDegree : degree H x = 5 := by omega
    exact eightRows_degreeFive_impossible
      hHClutter hHCard hHRows hBRows hBCard hDegree
  · intro x
    have hUpper := hDegreeFive.2 x
    by_contra hnot
    have hDegree : degree (blocker H) x = 5 := by omega
    have hDualClutter := blocker_isClutter H
    have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
      simpa [blocker_involution hHClutter] using hHRows
    have hDualCard : (blocker (blocker H)).card = 8 := by
      simpa [blocker_involution hHClutter] using hHCard
    exact eightRows_degreeFive_impossible
      hDualClutter hBCard hBRows hDualRows hDualCard hDegree

end AiMathLab.P0054.G420
