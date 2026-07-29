import AiMathLab.P0054MiddleSevenEightBasics
import AiMathLab.P0054MiddleSevenEightFanoBranch

/-!
# The seven-plus-seven middle equality kernel

Both sides have maximum degree three, a three-point row exists, and one
orientation therefore contains the unique four-row `K₄` incidence kernel.
-/

namespace AiMathLab.P0054.MiddleSevenSeven

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenEightBasics
open AiMathLab.P0054.MiddleSevenEightFinite
open AiMathLab.P0054.MiddleSevenEightFanoBranch

theorem sevenSeven_maxDegreeAtMost_three {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7) :
    MaxDegreeAtMost H 3 := by
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

theorem sevenSeven_has_three_row {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHCard : H.card = 7)
    (hBCard : (blocker H).card = 7)
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
  have hIndexCard : indices.card = 14 := by
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
      14 * 2 ^ (Fintype.card α - 4) := by
    calc
      (∑ i ∈ indices, (middleEvent i).card) ≤
          indices.card * 2 ^ (Fintype.card α - 4) :=
        Finset.sum_le_card_nsmul indices _ _ hEventBound
      _ = 14 * 2 ^ (Fintype.card α - 4) := by rw [hIndexCard]
  have hPositive : 0 < 2 ^ (Fintype.card α - 4) :=
    pow_pos (by decide : 0 < (2 : Nat)) _
  rw [hPower] at hCoverCard
  omega

theorem sevenSeven_has_k4_kernel {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 7) :
    (∃ x : α, degree H x = 3 ∧
      ∃ rowOrder : Fin 4 ≃ avoidPoint H x,
        (fourActualSupportMultiplicity rowOrder).toList = sevenEightK4Values) ∨
    (∃ x : α, degree (blocker H) x = 3 ∧
      ∃ rowOrder : Fin 4 ≃ avoidPoint (blocker H) x,
        (fourActualSupportMultiplicity rowOrder).toList = sevenEightK4Values) := by
  classical
  have hHMax := sevenSeven_maxDegreeAtMost_three
    hHClutter hHCard hHRows hBRows hBCard
  have hDualClutter : IsClutter (blocker H) := blocker_isClutter H
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHRows
  have hDualCard : (blocker (blocker H)).card = 7 := by
    simpa [blocker_involution hHClutter] using hHCard
  have hDoubleMax : MaxDegreeAtMost (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHMax
  have hBMax := sevenSeven_maxDegreeAtMost_three
    hDualClutter hBCard hBRows hDualRows hDualCard
  have kernel_values {K : G413.Hypergraph α}
      (hKClutter : IsClutter K)
      (hKCard : K.card = 7)
      (hKRows : RowsCardAtLeast K 3)
      (hBKRows : RowsCardAtLeast (blocker K) 3)
      (hBKCard : (blocker K).card = 7)
      (hBKMax : MaxDegreeAtMost (blocker K) 3)
      {x : α} (hDegree : degree K x = 3) :
      ∃ rowOrder : Fin 4 ≃ avoidPoint K x,
        (fourActualSupportMultiplicity rowOrder).toList = sevenEightK4Values := by
    let L := avoidPoint K x
    have hLCard : L.card = 4 := by
      have hPartition := card_avoidPoint_add_degree K x
      simpa [L, hKCard, hDegree] using hPartition
    have hLClutter : IsClutter L := by
      simpa [L] using avoidPoint_isClutter hKClutter x
    have hLRows : RowsCardAtLeast L 3 := by
      intro row hRow
      exact hKRows row (mem_avoidPoint.mp (by simpa [L] using hRow)).1
    have hBLRows : RowsCardAtLeast (blocker L) 2 := by
      simpa [L] using blocker_avoidPoint_rows_cardAtLeast_two hBKRows x
    have hLUpper : ∀ row ∈ L, row.card ≤ 8 := by
      intro row hRow
      have hRowK : row ∈ K :=
        (mem_avoidPoint.mp (by simpa [L] using hRow)).1
      have hRowDouble : row ∈ blocker (blocker K) := by
        simpa [blocker_involution hKClutter] using hRowK
      have hUpper := minimalTransversal_card_le_rows (mem_blocker.mp hRowDouble)
      omega
    have hBLUpper : (blocker L).card ≤ 8 := by
      have hLift := blocker_avoidPoint_card_le_blocker K x
      have : (blocker L).card ≤ 7 := by simpa [L, hBKCard] using hLift
      omega
    have hPairUpper : (pairRows (blocker L)).card ≤ 3 := by
      calc
        (pairRows (blocker L)).card ≤ degree (blocker K) x := by
          simpa [L] using
            pairRows_blocker_avoidPoint_card_le_degree hBKRows x
        _ ≤ 3 := hBKMax x
    let rowOrder := fourRowOrder hLCard
    exact ⟨rowOrder, sevenEight_actual_values_eq_k4 rowOrder hLClutter
      hBLRows hLRows hLUpper hBLUpper hPairUpper⟩
  rcases sevenSeven_has_three_row hHCard hBCard hHRows hBRows with
      ⟨T, hTH, hTCard⟩ | ⟨T, hTB, hTCard⟩
  · have hTDouble : T ∈ blocker (blocker H) := by
      rw [blocker_involution hHClutter]
      exact hTH
    obtain ⟨x, hxT, hDegree⟩ :=
      exists_degree_three_mem_three_blocker_row_of_card_seven
        hTDouble hTCard hBCard hBMax
    exact Or.inr ⟨x, hDegree, kernel_values hDualClutter hBCard hBRows
      hDualRows hDualCard hDoubleMax hDegree⟩
  · obtain ⟨x, hxT, hDegree⟩ :=
      exists_degree_three_mem_three_blocker_row_of_card_seven
        hTB hTCard hHCard hHMax
    exact Or.inl ⟨x, hDegree, kernel_values hHClutter hHCard hHRows
      hBRows hBCard hBMax hDegree⟩

end AiMathLab.P0054.MiddleSevenSeven
