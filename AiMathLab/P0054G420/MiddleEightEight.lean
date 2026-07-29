import AiMathLab.P0054G420.MiddleFourDegreeFourExclusion
import AiMathLab.P0054G420.MiddleThreeRow
import AiMathLab.P0054G413.FiveRowKernel

namespace AiMathLab.P0054.G420

open G413 G419

def FiveRowPairExactPrinciple (alpha : Type*)
    [Fintype alpha] [DecidableEq alpha] : Prop :=
  ∀ {K : G413.Hypergraph alpha},
    IsClutter K →
    K.card = 5 →
    RowsCardAtLeast K 3 →
    MaxDegreeAtMost K 3 →
    (blocker K).card ≤ 8 →
    (pairRows (blocker K)).card ≤ 3 →
    (pairRows (blocker K)).card = 3

theorem exists_degree_three_mem_three_blocker_row {alpha : Type*}
    [Fintype alpha] [DecidableEq alpha]
    {E : G413.Hypergraph alpha} {T : G413.Row alpha}
    (hT : T ∈ blocker E)
    (hTCard : T.card = 3)
    (hECard : E.card = 8)
    (hMaxDegree : MaxDegreeAtMost E 3) :
    ∃ x ∈ T, degree E x = 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hTForm⟩ :=
    Finset.card_eq_three.mp hTCard
  subst T
  let aRows := E.filter fun row ↦ a ∈ row
  let bRows := E.filter fun row ↦ b ∈ row
  let cRows := E.filter fun row ↦ c ∈ row
  have hCover : E ⊆ (aRows ∪ bRows) ∪ cRows := by
    intro row hRow
    obtain ⟨x, hxT, hxRow⟩ := (mem_blocker.mp hT).prop row hRow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with rfl | rfl | rfl
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hRow, hxRow⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hRow, hxRow⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hRow, hxRow⟩)
  have hUnionUpper : ((aRows ∪ bRows) ∪ cRows).card ≤
      aRows.card + bRows.card + cRows.card := by
    calc
      ((aRows ∪ bRows) ∪ cRows).card ≤
          (aRows ∪ bRows).card + cRows.card := Finset.card_union_le _ _
      _ ≤ (aRows.card + bRows.card) + cRows.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hSum : 8 ≤ degree E a + degree E b + degree E c := by
    have hCard := (Finset.card_le_card hCover).trans hUnionUpper
    rw [hECard] at hCard
    simpa [aRows, bRows, cRows, degree] using hCard
  by_cases ha : degree E a = 3
  · exact ⟨a, by simp, ha⟩
  by_cases hb : degree E b = 3
  · exact ⟨b, by simp, hb⟩
  by_cases hc : degree E c = 3
  · exact ⟨c, by simp, hc⟩
  have haUpper := hMaxDegree a
  have hbUpper := hMaxDegree b
  have hcUpper := hMaxDegree c
  omega

theorem eightEight_threeRow_impossible_of_fiveRowPairExact
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {D : G413.Hypergraph alpha}
    (hPairExact : FiveRowPairExactPrinciple alpha)
    (hDClutter : IsClutter D)
    (hDCard : D.card = 8)
    (hDRows : RowsCardAtLeast D 3)
    (hDMaxDegree : MaxDegreeAtMost D 3)
    (hECard : (blocker D).card = 8)
    (hERows : RowsCardAtLeast (blocker D) 3)
    (hEMaxDegree : MaxDegreeAtMost (blocker D) 3)
    {T : G413.Row alpha} (hTD : T ∈ D) (hTCard : T.card = 3) :
    False := by
  classical
  let E := blocker D
  have hDouble : blocker E = D := by
    simpa [E] using blocker_involution hDClutter
  have hTBlocker : T ∈ blocker E := by
    rw [hDouble]
    exact hTD
  obtain ⟨x, hxT, hDegreeE⟩ :=
    exists_degree_three_mem_three_blocker_row
      hTBlocker hTCard (by simpa [E] using hECard)
        (by simpa [E] using hEMaxDegree)
  let K := avoidPoint E x
  have hKCard : K.card = 5 := by
    have hPartition := card_avoidPoint_add_degree E x
    simpa [K, hDegreeE, E, hECard] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using G419.avoidPoint_isClutter (blocker_isClutter D) x
  have hKRows : RowsCardAtLeast K 3 := by
    intro row hRow
    have hRowE : row ∈ E :=
      (mem_avoidPoint.mp (by simpa [K] using hRow)).1
    change row ∈ blocker D at hRowE
    exact hERows row hRowE
  have hBlockerERows : RowsCardAtLeast (blocker E) 3 := by
    rw [hDouble]
    exact hDRows
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using
      G419.blocker_avoidPoint_rows_cardAtLeast_two hBlockerERows x
  have hKDegree : MaxDegreeAtMost K 3 := by
    intro y
    apply (degree_mono (H := K) (K := E) ?_ y).trans (hEMaxDegree y)
    intro row hRow
    exact (mem_avoidPoint.mp (by simpa [K] using hRow)).1
  have hPairUpper : (pairRows (blocker K)).card ≤ 3 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker E) x := by
        simpa [K] using
          G419.pairRows_blocker_avoidPoint_card_le_degree hBlockerERows x
      _ = degree D x := by rw [hDouble]
      _ ≤ 3 := hDMaxDegree x
  have hBlockerUpper : (blocker K).card ≤ 8 := by
    calc
      (blocker K).card ≤ (blocker E).card := by
        simpa [K] using G419.blocker_avoidPoint_card_le_blocker E x
      _ = 8 := by rw [hDouble, hDCard]
  have hPairs : (pairRows (blocker K)).card = 3 :=
    hPairExact hKClutter hKCard hKRows hKDegree hBlockerUpper hPairUpper
  have hxK : ∀ row ∈ K, x ∉ row := by
    intro row hRow
    exact (mem_avoidPoint.mp (by simpa [K] using hRow)).2
  let pairLifts := (pairRows (blocker K)).image (avoidBlockerLift E x)
  have hPairLiftsSubset : pairLifts ⊆ D.filter fun row ↦ x ∈ row := by
    intro lifted hLifted
    obtain ⟨row, hRowPair, rfl⟩ := Finset.mem_image.mp hLifted
    obtain ⟨hRowBlocker, hRowCard⟩ := Finset.mem_filter.mp hRowPair
    have hLiftBlocker : avoidBlockerLift E x row ∈ blocker E :=
      G419.avoidBlockerLift_mem_blocker hRowBlocker
    have hLiftD : avoidBlockerLift E x row ∈ D := by
      rw [← hDouble]
      exact hLiftBlocker
    refine Finset.mem_filter.mpr ⟨hLiftD, ?_⟩
    unfold avoidBlockerLift
    split
    · rename_i hTransversal
      exact (false_of_small_transversal hBlockerERows hTransversal
        (by omega)).elim
    · simp
  have hPairLiftsCard : pairLifts.card = 3 := by
    calc
      pairLifts.card = (pairRows (blocker K)).card := by
        apply Finset.card_image_iff.mpr
        exact (G419.avoidBlockerLift_injective E x).mono
          (Finset.filter_subset _ _)
      _ = 3 := hPairs
  have hDContainingCard : (D.filter fun row ↦ x ∈ row).card = 3 := by
    change degree D x = 3
    have hLower := Finset.card_le_card hPairLiftsSubset
    rw [hPairLiftsCard] at hLower
    have hLowerDegree : 3 ≤ degree D x := by
      simpa [degree] using hLower
    have hUpper := hDMaxDegree x
    omega
  have hPairLiftsEq : pairLifts = D.filter fun row ↦ x ∈ row := by
    apply Finset.eq_of_subset_of_card_le hPairLiftsSubset
    rw [hPairLiftsCard, hDContainingCard]
  have hForcedBase : G413.forcedBase (blocker K) x ⊆ D := by
    intro lifted hLifted
    obtain ⟨row, hRowBlocker, rfl⟩ := Finset.mem_image.mp hLifted
    have hAvoidLiftD : avoidBlockerLift E x row ∈ D := by
      rw [← hDouble]
      exact G419.avoidBlockerLift_mem_blocker hRowBlocker
    by_cases hRowPair : row.card = 2
    · have hNotTransversal : ¬IsTransversal E row := by
        intro hTransversal
        exact false_of_small_transversal hBlockerERows hTransversal (by omega)
      simpa [G413.liftPairRow, hRowPair, avoidBlockerLift,
        hNotTransversal] using hAvoidLiftD
    · have hxAvoidLift : x ∉ avoidBlockerLift E x row := by
        intro hxLift
        have hInPairLifts : avoidBlockerLift E x row ∈ pairLifts := by
          rw [hPairLiftsEq]
          exact Finset.mem_filter.mpr ⟨hAvoidLiftD, hxLift⟩
        obtain ⟨pair, hPair, hPairLift⟩ := Finset.mem_image.mp hInPairLifts
        obtain ⟨hPairBlocker, hPairCard⟩ := Finset.mem_filter.mp hPair
        have hRowEq : row = pair :=
          G419.avoidBlockerLift_injective E x hRowBlocker hPairBlocker
            hPairLift.symm
        exact hRowPair (by simpa [hRowEq] using hPairCard)
      have hTransversal : IsTransversal E row := by
        by_contra hNotTransversal
        apply hxAvoidLift
        simp [avoidBlockerLift, hNotTransversal]
      simpa [G413.liftPairRow, hRowPair, avoidBlockerLift,
        hTransversal] using hAvoidLiftD
  have hKD : K ⊆ blocker D := by
    intro row hRow
    exact (mem_avoidPoint.mp (by simpa [K, E] using hRow)).1
  have hCompletion : G413.IsKernelCompletion K x D := by
    exact ⟨hDClutter, hDCard, hDRows, hDMaxDegree, hKDegree,
      hForcedBase, hKD⟩
  exact (G413.no_kernel_completion_of_eight
    hKClutter hKCard hKRows hxK hBKRows hPairs hBlockerUpper)
      ⟨D, hCompletion⟩

theorem eightEight_impossible_of_fiveRowPairExact
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {H : G413.Hypergraph alpha}
    (hPairExact : FiveRowPairExactPrinciple alpha)
    (hHClutter : IsClutter H)
    (hHCard : H.card = 8)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 8) :
    False := by
  have hDegrees := middle_maxDegreesAtMost_three
    hHClutter hHCard hHRows hBRows hBCard
  have hThree := middle_has_three_row hHClutter (by omega) hHRows hBRows
  rcases hThree with ⟨T, hTH, hTCard⟩ | ⟨T, hTB, hTCard⟩
  · exact eightEight_threeRow_impossible_of_fiveRowPairExact
      hPairExact hHClutter hHCard hHRows hDegrees.1 hBCard hBRows
        hDegrees.2 hTH hTCard
  · have hDualClutter := blocker_isClutter H
    have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
      simpa [blocker_involution hHClutter] using hHRows
    have hDualCard : (blocker (blocker H)).card = 8 := by
      simpa [blocker_involution hHClutter] using hHCard
    have hDualDegree : MaxDegreeAtMost (blocker (blocker H)) 3 := by
      simpa [blocker_involution hHClutter] using hDegrees.1
    exact eightEight_threeRow_impossible_of_fiveRowPairExact
      hPairExact hDualClutter hBCard hBRows hDegrees.2 hDualCard hDualRows
        hDualDegree hTB hTCard

end AiMathLab.P0054.G420
