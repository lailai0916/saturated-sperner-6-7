import AiMathLab.P0054G419.BlockerDegree

namespace AiMathLab.P0054.G419

open G413

def OrderedThreeKernelProfile
    (p q r x12 x13 x23 : Nat) : Prop :=
  (p = 1 ∧ q = 1 ∧ r = 1 ∧ x12 = 1 ∧ x13 = 1 ∧ x23 = 1) ∨
  (p = 1 ∧ q = 2 ∧ r = 2 ∧ x12 = 1 ∧ x13 = 1 ∧ x23 = 0) ∨
  (p = 2 ∧ q = 1 ∧ r = 2 ∧ x12 = 1 ∧ x13 = 0 ∧ x23 = 1) ∨
  (p = 2 ∧ q = 2 ∧ r = 1 ∧ x12 = 0 ∧ x13 = 1 ∧ x23 = 1) ∨
  (p = 1 ∧ q = 1 ∧ r = 3 ∧ x12 = 2 ∧ x13 = 0 ∧ x23 = 0) ∨
  (p = 1 ∧ q = 3 ∧ r = 1 ∧ x12 = 0 ∧ x13 = 2 ∧ x23 = 0) ∨
  (p = 3 ∧ q = 1 ∧ r = 1 ∧ x12 = 0 ∧ x13 = 0 ∧ x23 = 2)

instance orderedThreeKernelProfileDecidable
    (p q r x12 x13 x23 : Nat) :
    Decidable (OrderedThreeKernelProfile p q r x12 x13 x23) := by
  unfold OrderedThreeKernelProfile
  infer_instance

def kernelCap (n : Nat) : Fin 5 :=
  ⟨min n 4, by
    have h := Nat.min_le_right n 4
    omega⟩

theorem kernelCap_le (n : Nat) : (kernelCap n).val ≤ n := by
  exact Nat.min_le_left n 4

theorem kernelCap_sum_three
    (a b c : Nat) (h : 3 ≤ a + b + c) :
    3 ≤ (kernelCap a).val + (kernelCap b).val + (kernelCap c).val := by
  by_cases ha : a ≤ 4 <;> by_cases hb : b ≤ 4 <;> by_cases hc : c ≤ 4
  all_goals simp [kernelCap, Nat.min_def, *] <;> omega

theorem kernelCap_sum_pos
    (a b : Nat) (h : 0 < a + b) :
    0 < (kernelCap a).val + (kernelCap b).val := by
  by_cases ha : a ≤ 4 <;> by_cases hb : b ≤ 4
  all_goals simp [kernelCap, Nat.min_def, *]

theorem eq_of_kernelCap_eq {n k : Nat}
    (hk : k < 4) (h : (kernelCap n).val = k) : n = k := by
  by_cases hn : n ≤ 4
  · simpa [kernelCap, Nat.min_eq_left hn] using h
  · have hFour : 4 ≤ n := by omega
    simp [kernelCap, Nat.min_eq_right hFour] at h
    omega

set_option maxRecDepth 100000 in
set_option maxSynthPendingDepth 100 in
set_option maxHeartbeats 100000000 in
-- Kernel evaluation checks all 15625 capped incidence vectors.
theorem orderedThreeKernelProfile_finite :
    ∀ p q r x12 x13 x23 : Fin 5,
      3 ≤ p.val + x12.val + x13.val →
      3 ≤ q.val + x12.val + x23.val →
      3 ≤ r.val + x13.val + x23.val →
      0 < p.val + x13.val → 0 < q.val + x23.val →
      0 < p.val + x12.val → 0 < r.val + x23.val →
      0 < q.val + x12.val → 0 < r.val + x13.val →
      x12.val * x13.val + x12.val * x23.val + x13.val * x23.val +
          x12.val * r.val + x13.val * q.val + x23.val * p.val ≤ 6 →
      x12.val * x13.val + x12.val * x23.val + x13.val * x23.val +
          x12.val * r.val + x13.val * q.val + x23.val * p.val +
          p.val * q.val * r.val ≤ 10 →
      OrderedThreeKernelProfile
        p.val q.val r.val x12.val x13.val x23.val := by
  decide

theorem orderedThreeKernelProfile_of_bounds
    (p q r x12 x13 x23 : Nat)
    (hA : 3 ≤ p + x12 + x13)
    (hB : 3 ≤ q + x12 + x23)
    (hC : 3 ≤ r + x13 + x23)
    (hAB : 0 < p + x13) (hBA : 0 < q + x23)
    (hAC : 0 < p + x12) (hCA : 0 < r + x23)
    (hBC : 0 < q + x12) (hCB : 0 < r + x13)
    (hPair :
      x12 * x13 + x12 * x23 + x13 * x23 +
        x12 * r + x13 * q + x23 * p ≤ 6)
    (hTotal :
      x12 * x13 + x12 * x23 + x13 * x23 +
        x12 * r + x13 * q + x23 * p + p * q * r ≤ 10) :
    OrderedThreeKernelProfile p q r x12 x13 x23 := by
  have hPairCapped :
      (kernelCap x12).val * (kernelCap x13).val +
          (kernelCap x12).val * (kernelCap x23).val +
          (kernelCap x13).val * (kernelCap x23).val +
          (kernelCap x12).val * (kernelCap r).val +
          (kernelCap x13).val * (kernelCap q).val +
          (kernelCap x23).val * (kernelCap p).val ≤ 6 := by
    calc
      (kernelCap x12).val * (kernelCap x13).val +
            (kernelCap x12).val * (kernelCap x23).val +
            (kernelCap x13).val * (kernelCap x23).val +
            (kernelCap x12).val * (kernelCap r).val +
            (kernelCap x13).val * (kernelCap q).val +
            (kernelCap x23).val * (kernelCap p).val ≤
          x12 * x13 + x12 * x23 + x13 * x23 +
            x12 * r + x13 * q + x23 * p := by
        gcongr <;> exact kernelCap_le _
      _ ≤ 6 := hPair
  have hTotalCapped :
      (kernelCap x12).val * (kernelCap x13).val +
          (kernelCap x12).val * (kernelCap x23).val +
          (kernelCap x13).val * (kernelCap x23).val +
          (kernelCap x12).val * (kernelCap r).val +
          (kernelCap x13).val * (kernelCap q).val +
          (kernelCap x23).val * (kernelCap p).val +
          (kernelCap p).val * (kernelCap q).val * (kernelCap r).val ≤ 10 := by
    calc
      (kernelCap x12).val * (kernelCap x13).val +
            (kernelCap x12).val * (kernelCap x23).val +
            (kernelCap x13).val * (kernelCap x23).val +
            (kernelCap x12).val * (kernelCap r).val +
            (kernelCap x13).val * (kernelCap q).val +
            (kernelCap x23).val * (kernelCap p).val +
            (kernelCap p).val * (kernelCap q).val * (kernelCap r).val ≤
          x12 * x13 + x12 * x23 + x13 * x23 +
            x12 * r + x13 * q + x23 * p + p * q * r := by
        gcongr <;> exact kernelCap_le _
      _ ≤ 10 := hTotal
  have hFinite := orderedThreeKernelProfile_finite
    (kernelCap p) (kernelCap q) (kernelCap r)
    (kernelCap x12) (kernelCap x13) (kernelCap x23)
    (kernelCap_sum_three p x12 x13 hA)
    (kernelCap_sum_three q x12 x23 hB)
    (kernelCap_sum_three r x13 x23 hC)
    (kernelCap_sum_pos p x13 hAB) (kernelCap_sum_pos q x23 hBA)
    (kernelCap_sum_pos p x12 hAC) (kernelCap_sum_pos r x23 hCA)
    (kernelCap_sum_pos q x12 hBC) (kernelCap_sum_pos r x13 hCB)
    hPairCapped hTotalCapped
  unfold OrderedThreeKernelProfile at hFinite ⊢
  rcases hFinite with h | h | h | h | h | h | h
  · left
    rcases h with ⟨hp, hq, hr, hx12, hx13, hx23⟩
    exact ⟨eq_of_kernelCap_eq (by omega) hp,
      eq_of_kernelCap_eq (by omega) hq,
      eq_of_kernelCap_eq (by omega) hr,
      eq_of_kernelCap_eq (by omega) hx12,
      eq_of_kernelCap_eq (by omega) hx13,
      eq_of_kernelCap_eq (by omega) hx23⟩
  · right; left
    rcases h with ⟨hp, hq, hr, hx12, hx13, hx23⟩
    exact ⟨eq_of_kernelCap_eq (by omega) hp,
      eq_of_kernelCap_eq (by omega) hq,
      eq_of_kernelCap_eq (by omega) hr,
      eq_of_kernelCap_eq (by omega) hx12,
      eq_of_kernelCap_eq (by omega) hx13,
      eq_of_kernelCap_eq (by omega) hx23⟩
  · right; right; left
    rcases h with ⟨hp, hq, hr, hx12, hx13, hx23⟩
    exact ⟨eq_of_kernelCap_eq (by omega) hp,
      eq_of_kernelCap_eq (by omega) hq,
      eq_of_kernelCap_eq (by omega) hr,
      eq_of_kernelCap_eq (by omega) hx12,
      eq_of_kernelCap_eq (by omega) hx13,
      eq_of_kernelCap_eq (by omega) hx23⟩
  · right; right; right; left
    rcases h with ⟨hp, hq, hr, hx12, hx13, hx23⟩
    exact ⟨eq_of_kernelCap_eq (by omega) hp,
      eq_of_kernelCap_eq (by omega) hq,
      eq_of_kernelCap_eq (by omega) hr,
      eq_of_kernelCap_eq (by omega) hx12,
      eq_of_kernelCap_eq (by omega) hx13,
      eq_of_kernelCap_eq (by omega) hx23⟩
  · right; right; right; right; left
    rcases h with ⟨hp, hq, hr, hx12, hx13, hx23⟩
    exact ⟨eq_of_kernelCap_eq (by omega) hp,
      eq_of_kernelCap_eq (by omega) hq,
      eq_of_kernelCap_eq (by omega) hr,
      eq_of_kernelCap_eq (by omega) hx12,
      eq_of_kernelCap_eq (by omega) hx13,
      eq_of_kernelCap_eq (by omega) hx23⟩
  · right; right; right; right; right; left
    rcases h with ⟨hp, hq, hr, hx12, hx13, hx23⟩
    exact ⟨eq_of_kernelCap_eq (by omega) hp,
      eq_of_kernelCap_eq (by omega) hq,
      eq_of_kernelCap_eq (by omega) hr,
      eq_of_kernelCap_eq (by omega) hx12,
      eq_of_kernelCap_eq (by omega) hx13,
      eq_of_kernelCap_eq (by omega) hx23⟩
  · right; right; right; right; right; right
    rcases h with ⟨hp, hq, hr, hx12, hx13, hx23⟩
    exact ⟨eq_of_kernelCap_eq (by omega) hp,
      eq_of_kernelCap_eq (by omega) hq,
      eq_of_kernelCap_eq (by omega) hr,
      eq_of_kernelCap_eq (by omega) hx12,
      eq_of_kernelCap_eq (by omega) hx13,
      eq_of_kernelCap_eq (by omega) hx23⟩

theorem pairRows_blocker_avoidPoint_card_le_degree {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (x : α) :
    (pairRows (blocker (avoidPoint H x))).card ≤ degree (blocker H) x := by
  classical
  let liftedPairs :=
    (pairRows (blocker (avoidPoint H x))).image (avoidBlockerLift H x)
  have hLiftedCard :
      liftedPairs.card = (pairRows (blocker (avoidPoint H x))).card := by
    change ((pairRows (blocker (avoidPoint H x))).image
      (avoidBlockerLift H x)).card = _
    rw [Finset.card_image_iff.mpr]
    intro T hT U hU hEq
    exact avoidBlockerLift_injective H x
      (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hU).1 hEq
  have hLiftedSubset :
      liftedPairs ⊆ (blocker H).filter fun E ↦ x ∈ E := by
    intro T hT
    obtain ⟨U, hUPair, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hUBlocker, hUCard⟩ := Finset.mem_filter.mp hUPair
    refine Finset.mem_filter.mpr ⟨avoidBlockerLift_mem_blocker hUBlocker, ?_⟩
    unfold avoidBlockerLift
    split
    · rename_i hTransversal
      exact (false_of_small_transversal hBRows hTransversal (by omega)).elim
    · simp
  calc
    (pairRows (blocker (avoidPoint H x))).card = liftedPairs.card := hLiftedCard.symm
    _ ≤ degree (blocker H) x := by
      rw [degree]
      exact Finset.card_le_card hLiftedSubset

theorem pairRows_blocker_avoidPoint_card_le_six {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10)
    (x : α) :
    (pairRows (blocker (avoidPoint H x))).card ≤ 6 := by
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    rw [blocker_involution hHClutter]
    exact hHRows
  have hDualCard : (blocker (blocker H)).card = 6 := by
    rw [blocker_involution hHClutter]
    exact hHCard
  have hBlockerDegree : degree (blocker H) x ≤ 6 :=
    blockerSide_maxDegreeAtMost_six
      (blocker_isClutter H) hBCard hBRows hDualRows hDualCard x
  exact (pairRows_blocker_avoidPoint_card_le_degree hBRows x).trans hBlockerDegree

theorem sixTen_degreeThree_kernel_profile {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 6)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 10)
    {x : α} (hDegree : degree H x = 3) :
    ∃ A B C : Row α,
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      avoidPoint H x = {A, B, C} ∧
      OrderedThreeKernelProfile
        (privatePart A B C).card
        (privatePart B A C).card
        (privatePart C A B).card
        (sharedPart A B C).card
        (sharedPart A C B).card
        (sharedPart B C A).card := by
  classical
  let K := avoidPoint H x
  have hKCard : K.card = 3 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  obtain ⟨A, B, C, hAB, hAC, hBC, hK⟩ := Finset.card_eq_three.mp hKCard
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hEK
    exact hHRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
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
  have hBCard' := hKRows B hBK
  have hCCard := hKRows C hCK
  rw [threePart_union_card hNoCommon] at hACard
  rw [threePart_union_card_second hNoCommon] at hBCard'
  rw [threePart_union_card_third hNoCommon] at hCCard
  have hPairRowsUpper : (pairRows (blocker K)).card ≤ 6 := by
    simpa [K] using pairRows_blocker_avoidPoint_card_le_six
      hHClutter hHCard hHRows hBRows hBCard x
  have hPair :
      (sharedPart A B C).card * (sharedPart A C B).card +
          (sharedPart A B C).card * (sharedPart B C A).card +
          (sharedPart A C B).card * (sharedPart B C A).card +
          (sharedPart A B C).card * (privatePart C A B).card +
          (sharedPart A C B).card * (privatePart B A C).card +
          (sharedPart B C A).card * (privatePart A B C).card ≤ 6 :=
    (threePairGenerated_card_le_pairRows hK).trans hPairRowsUpper
  have hBlockerUpper : (blocker K).card ≤ 10 := by
    have hLift := blocker_avoidPoint_card_le_blocker H x
    simpa [K, hBCard] using hLift
  have hTotal :
      (sharedPart A B C).card * (sharedPart A C B).card +
          (sharedPart A B C).card * (sharedPart B C A).card +
          (sharedPart A C B).card * (sharedPart B C A).card +
          (sharedPart A B C).card * (privatePart C A B).card +
          (sharedPart A C B).card * (privatePart B A C).card +
          (sharedPart B C A).card * (privatePart A B C).card +
          (privatePart A B C).card *
            (privatePart B A C).card *
            (privatePart C A B).card ≤ 10 :=
    (threeGeneratedRows_card_le_blocker hK hAB hAC hBC).trans hBlockerUpper
  refine ⟨A, B, C, hAB, hAC, hBC, by simpa [K] using hK, ?_⟩
  exact orderedThreeKernelProfile_of_bounds
    (privatePart A B C).card
    (privatePart B A C).card
    (privatePart C A B).card
    (sharedPart A B C).card
    (sharedPart A C B).card
    (sharedPart B C A).card
    hACard hBCard' hCCard hPY hQZ hPX hRZ hQX hRY hPair hTotal

end AiMathLab.P0054.G419
