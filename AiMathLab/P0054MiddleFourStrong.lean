import AiMathLab.P0054MiddleLower
import AiMathLab.P0054Sat6
import AiMathLab.P0054AdjacentLower

/-!
# A strong four-row middle endpoint

Four rows of size at least three, with no blocker row smaller than three,
have at least fourteen blockers.  The degree-two case is reduced to the
already formalized `m(2,3) ≥ 9` bound on the residual clutter.
-/

namespace AiMathLab.P0054.MiddleFourStrong

open AiMathLab.P0054.G413

theorem blocker_card_ge_fourteen {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 4)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    14 ≤ (blocker H).card := by
  classical
  have hDegreeUpper :=
    AiMathLab.P0054.MiddleLower.fourRow_maxDegreeAtMost_two
      hHCard hHRows hBRows
  by_cases hAtMostOne : MaxDegreeAtMost H 1
  · obtain ⟨A, B, C, D, hAB, hAC, hAD, hBC, hBD, hCD, hH⟩ :=
      Finset.card_eq_four.mp hHCard
    have pair_disjoint {R S : G413.Row α}
        (hR : R ∈ H) (hS : S ∈ H) (hRS : R ≠ S) :
        Disjoint R S := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hTwo :=
        AiMathLab.P0054.MiddleLower.degree_ge_two_of_two_rows
          hR hS hRS (Finset.mem_inter.mp hx).1
            (Finset.mem_inter.mp hx).2
      have hOne := hAtMostOne x
      omega
    have hAH : A ∈ H := by simp [hH]
    have hBH : B ∈ H := by simp [hH]
    have hCH : C ∈ H := by simp [hH]
    have hDH : D ∈ H := by simp [hH]
    have hProduct :=
      AiMathLab.P0054.AdjacentLower.fourRow_product_le_blocker hH
        (pair_disjoint hAH hBH hAB)
        (pair_disjoint hAH hCH hAC)
        (pair_disjoint hAH hDH hAD)
        (pair_disjoint hBH hCH hBC)
        (pair_disjoint hBH hDH hBD)
        (pair_disjoint hCH hDH hCD)
    have hA := hHRows A hAH
    have hB := hHRows B hBH
    have hC := hHRows C hCH
    have hD := hHRows D hDH
    have hEightyOne : 81 ≤ A.card * B.card * C.card * D.card := by
      calc
        81 = 3 * 3 * 3 * 3 := by norm_num
        _ ≤ A.card * B.card * C.card * D.card := by gcongr
    omega
  · unfold MaxDegreeAtMost at hAtMostOne
    push Not at hAtMostOne
    obtain ⟨x, hx⟩ := hAtMostOne
    have hDegree : degree H x = 2 := by
      have hUpper := hDegreeUpper x
      omega
    have hAvoidCard : (avoidPoint H x).card = 2 := by
      have hPartition := card_avoidPoint_add_degree H x
      omega
    have hContaining : 9 ≤ degree (blocker H) x :=
      AiMathLab.P0054.G415.twoAvoidingRows_blockers_containing_card_ge_nine
        hHRows hBRows hAvoidCard
    let R := residual H x
    have hRClutter : IsClutter R := by
      simpa [R] using residual_isClutter H x
    have hRRows : RowsCardAtLeast R 2 := by
      simpa [R] using residual_rows_cardAtLeast hHRows x
    have hBlockerR : blocker R = avoidPoint (blocker H) x := by
      simpa [R] using blocker_residual H x
    have hBlockerRRows : RowsCardAtLeast (blocker R) 3 := by
      intro E hE
      rw [hBlockerR] at hE
      exact hBRows E (mem_avoidPoint.mp hE).1
    have hResidualTotal : 9 ≤ R.card + (blocker R).card :=
      AiMathLab.P0054.Sat6.local_lower R (blocker R)
        hRClutter (blocker_isClutter R)
        (blocker_involution hRClutter).symm rfl hRRows hBlockerRRows
    have hRCard : R.card ≤ 4 := by
      calc
        R.card ≤ H.card := by simpa [R] using residual_card_le H x
        _ = 4 := hHCard
    have hAvoiding : 5 ≤ (avoidPoint (blocker H) x).card := by
      rw [← hBlockerR]
      omega
    have hPartition := card_avoidPoint_add_degree (blocker H) x
    omega

end AiMathLab.P0054.MiddleFourStrong
