import AiMathLab.P0054MiddleSevenEightFanoBranch
import AiMathLab.P0054G420.MiddleEightEightActual

/-!
# The five-row-kernel branch of the seven-plus-eight exclusion

If a three-point row lies on the seven-row side, points of degree three
are excluded by the Fano argument.  A point of degree two leaves a
five-row kernel whose opposite eight-row family would be a forbidden
kernel completion.  Consequently all three points of the row have degree
one.  The row is then isolated, and the standard product injection gives
at least nine blockers, contradicting the assumed eight.
-/

namespace AiMathLab.P0054.MiddleSevenEightFiveKernelBranch

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightFanoBranch

theorem sevenRows_degreeTwo_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBCard : (blocker H).card = 8)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 3)
    {x : α} (hDegree : degree H x = 2) :
    False := by
  classical
  let K := avoidPoint H x
  have hDouble : blocker (blocker H) = H := blocker_involution hHClutter
  have hKCard : K.card = 5 := by
    have hPartition := card_avoidPoint_add_degree H x
    simpa [K, hHCard, hDegree] using hPartition
  have hKClutter : IsClutter K := by
    simpa [K] using avoidPoint_isClutter hHClutter x
  have hKRows : RowsCardAtLeast K 3 := by
    intro row hRow
    exact hHRows row (mem_avoidPoint.mp (by simpa [K] using hRow)).1
  have hBKRows : RowsCardAtLeast (blocker K) 2 := by
    simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
  have hKDegree : MaxDegreeAtMost K 3 := by
    intro y
    apply (degree_mono (H := K) (K := H) ?_ y).trans (hHMaxDegree y)
    intro row hRow
    exact (mem_avoidPoint.mp (by simpa [K] using hRow)).1
  have hPairUpper : (pairRows (blocker K)).card ≤ 3 := by
    calc
      (pairRows (blocker K)).card ≤ degree (blocker H) x := by
        simpa [K] using pairRows_blocker_avoidPoint_card_le_degree hBRows x
      _ ≤ 3 := hBMaxDegree x
  have hBlockerUpper : (blocker K).card ≤ 8 := by
    calc
      (blocker K).card ≤ (blocker H).card := by
        simpa [K] using blocker_avoidPoint_card_le_blocker H x
      _ = 8 := hBCard
  have hPairs : (pairRows (blocker K)).card = 3 :=
    fiveRowPairExactPrinciple α hKClutter hKCard hKRows hKDegree
      hBlockerUpper hPairUpper
  have hxK : ∀ row ∈ K, x ∉ row := by
    intro row hRow
    exact (mem_avoidPoint.mp (by simpa [K] using hRow)).2
  let pairLifts := (pairRows (blocker K)).image (avoidBlockerLift H x)
  have hPairLiftsSubset :
      pairLifts ⊆ (blocker H).filter fun row ↦ x ∈ row := by
    intro lifted hLifted
    obtain ⟨row, hRowPair, rfl⟩ := Finset.mem_image.mp hLifted
    obtain ⟨hRowBlocker, hRowCard⟩ := Finset.mem_filter.mp hRowPair
    refine Finset.mem_filter.mpr
      ⟨avoidBlockerLift_mem_blocker hRowBlocker, ?_⟩
    unfold avoidBlockerLift
    split
    · rename_i hTransversal
      exact (false_of_small_transversal hBRows hTransversal
        (by omega)).elim
    · simp
  have hPairLiftsCard : pairLifts.card = 3 := by
    calc
      pairLifts.card = (pairRows (blocker K)).card := by
        apply Finset.card_image_iff.mpr
        exact (avoidBlockerLift_injective H x).mono
          (Finset.filter_subset _ _)
      _ = 3 := hPairs
  have hBContainingCard :
      ((blocker H).filter fun row ↦ x ∈ row).card = 3 := by
    change degree (blocker H) x = 3
    have hLower := Finset.card_le_card hPairLiftsSubset
    rw [hPairLiftsCard] at hLower
    have hLowerDegree : 3 ≤ degree (blocker H) x := by
      simpa [degree] using hLower
    have hUpper := hBMaxDegree x
    omega
  have hPairLiftsEq :
      pairLifts = (blocker H).filter fun row ↦ x ∈ row := by
    apply Finset.eq_of_subset_of_card_le hPairLiftsSubset
    rw [hPairLiftsCard, hBContainingCard]
  have hForcedBase : G413.forcedBase (blocker K) x ⊆ blocker H := by
    intro lifted hLifted
    obtain ⟨row, hRowBlocker, rfl⟩ := Finset.mem_image.mp hLifted
    have hAvoidLiftB : avoidBlockerLift H x row ∈ blocker H :=
      avoidBlockerLift_mem_blocker hRowBlocker
    by_cases hRowPair : row.card = 2
    · have hNotTransversal : ¬IsTransversal H row := by
        intro hTransversal
        exact false_of_small_transversal hBRows hTransversal (by omega)
      simpa [G413.liftPairRow, hRowPair, avoidBlockerLift,
        hNotTransversal] using hAvoidLiftB
    · have hxAvoidLift : x ∉ avoidBlockerLift H x row := by
        intro hxLift
        have hInPairLifts : avoidBlockerLift H x row ∈ pairLifts := by
          rw [hPairLiftsEq]
          exact Finset.mem_filter.mpr ⟨hAvoidLiftB, hxLift⟩
        obtain ⟨pair, hPair, hPairLift⟩ :=
          Finset.mem_image.mp hInPairLifts
        obtain ⟨hPairBlocker, hPairCard⟩ := Finset.mem_filter.mp hPair
        have hRowEq : row = pair :=
          avoidBlockerLift_injective H x hRowBlocker hPairBlocker
            hPairLift.symm
        exact hRowPair (by simpa [hRowEq] using hPairCard)
      have hTransversal : IsTransversal H row := by
        by_contra hNotTransversal
        apply hxAvoidLift
        simp [avoidBlockerLift, hNotTransversal]
      simpa [G413.liftPairRow, hRowPair, avoidBlockerLift,
        hTransversal] using hAvoidLiftB
  have hKB : K ⊆ blocker (blocker H) := by
    intro row hRow
    rw [hDouble]
    exact (mem_avoidPoint.mp (by simpa [K] using hRow)).1
  have hCompletion : G413.IsKernelCompletion K x (blocker H) := by
    exact ⟨blocker_isClutter H, hBCard, hBRows, hBMaxDegree, hKDegree,
      hForcedBase, hKB⟩
  exact (G413.no_kernel_completion_of_eight hKClutter hKCard hKRows
    hxK hBKRows hPairs hBlockerUpper) ⟨blocker H, hCompletion⟩

theorem threeRow_on_sevenSide_impossible {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMaxDegree : MaxDegreeAtMost H 3)
    (hBCard : (blocker H).card = 8)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBMaxDegree : MaxDegreeAtMost (blocker H) 3)
    {T : G413.Row α} (hT : T ∈ H) (hTCard : T.card = 3) :
    False := by
  classical
  have hDegreeOne : ∀ x ∈ T, degree H x = 1 := by
    intro x hxT
    have hPositive : 0 < degree H x := by
      rw [degree]
      exact Finset.card_pos.mpr
        ⟨T, Finset.mem_filter.mpr ⟨hT, hxT⟩⟩
    have hUpper := hHMaxDegree x
    by_cases hThree : degree H x = 3
    · exact (sevenRows_degreeThree_impossible hHClutter hHCard hHRows
        hHMaxDegree hBCard hBRows hBMaxDegree hThree).elim
    by_cases hTwo : degree H x = 2
    · exact (sevenRows_degreeTwo_impossible hHClutter hHCard hHRows
        hHMaxDegree hBCard hBRows hBMaxDegree hTwo).elim
    omega
  let K := H.erase T
  have hKSubset : K ⊆ H := by
    simpa [K] using Finset.erase_subset T H
  have hKClutter : IsClutter K := hHClutter.mono hKSubset
  have hKCard : K.card = 6 := by
    simpa [K, Finset.card_erase_of_mem hT, hHCard]
  have hHK : H = insert T K := by
    simpa [K] using (Finset.insert_erase hT).symm
  have hTK : ∀ E ∈ K, Disjoint T E := by
    intro E hE
    obtain ⟨hET, hEH⟩ := Finset.mem_erase.mp (by simpa [K] using hE)
    rw [Finset.disjoint_left]
    intro x hxT hxE
    have hTwo : 2 ≤ degree H x :=
      degree_ge_two_of_two_rows hT hEH hET.symm hxT hxE
    have hOne := hDegreeOne x hxT
    omega
  have hKRows : RowsCardAtLeast K 3 := by
    intro E hE
    exact hHRows E (hKSubset hE)
  obtain ⟨E, hEK⟩ : K.Nonempty := Finset.card_pos.mp (by omega)
  have hEDual : E ∈ blocker (blocker K) := by
    rw [blocker_involution hKClutter]
    exact hEK
  have hKBlockers : 3 ≤ (blocker K).card := by
    exact (hKRows E hEK).trans
      (minimalTransversal_card_le_rows (mem_blocker.mp hEDual))
  have hProduct := isolatedRow_product_le_blocker_card hHK hTK
  have hNine : 9 ≤ (blocker H).card := by
    calc
      9 = 3 * 3 := rfl
      _ ≤ T.card * (blocker K).card :=
        Nat.mul_le_mul (by omega) hKBlockers
      _ ≤ (blocker H).card := hProduct
  omega

end AiMathLab.P0054.MiddleSevenEightFiveKernelBranch
