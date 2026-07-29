import AiMathLab.P0054MiddleSixProfile

/-!
# Degree bound on the nine-row side

This is the dual degree estimate needed for the middle split `6 + 9`.
-/

namespace AiMathLab.P0054.MiddleNineDegree

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419

theorem nineRows_maxDegreeAtMost_five {α : Type*}
    [Fintype α] [DecidableEq α]
    {G : G413.Hypergraph α}
    (hGClutter : IsClutter G)
    (hGCard : G.card = 9)
    (hGRows : RowsCardAtLeast G 3)
    (hBRows : RowsCardAtLeast (blocker G) 3)
    (hBCard : (blocker G).card = 6) :
    MaxDegreeAtMost G 5 := by
  classical
  intro x
  by_contra hDegreeUpper
  have hDegreeLower : 6 ≤ degree G x := by omega
  have hAvoidUpper : (avoidPoint G x).card ≤ 3 := by
    have hPartition := card_avoidPoint_add_degree G x
    omega
  interval_cases hAvoidCard : (avoidPoint G x).card
  · have hTransversal : IsTransversal G {x} := by
      intro E hEG
      have hxE : x ∈ E := by
        by_contra hxE
        have hEAvoid : E ∈ avoidPoint G x :=
          mem_avoidPoint.mpr ⟨hEG, hxE⟩
        have hPositive : 0 < (avoidPoint G x).card :=
          Finset.card_pos.mpr ⟨E, hEAvoid⟩
        omega
      exact ⟨x, by simp, hxE⟩
    exact false_of_small_transversal hBRows hTransversal (by simp)
  · obtain ⟨E, hAvoidEq⟩ := Finset.card_eq_one.mp hAvoidCard
    have hEAvoid : E ∈ avoidPoint G x := by simp [hAvoidEq]
    have hEG : E ∈ G := (mem_avoidPoint.mp hEAvoid).1
    have hEPositive : 0 < E.card := by
      have := hGRows E hEG
      omega
    obtain ⟨y, hyE⟩ := Finset.card_pos.mp hEPositive
    have hTransversal : IsTransversal G {x, y} := by
      intro A hAG
      by_cases hxA : x ∈ A
      · exact ⟨x, by simp, hxA⟩
      · have hAAvoid : A ∈ avoidPoint G x :=
          mem_avoidPoint.mpr ⟨hAG, hxA⟩
        have hAE : A = E := by simpa [hAvoidEq] using hAAvoid
        exact ⟨y, by simp, hAE ▸ hyE⟩
    exact false_of_small_transversal hBRows hTransversal
      ((Finset.card_le_two : ({x, y} : Row α).card ≤ 2).trans_lt (by omega))
  · have hNine : 9 ≤ degree (blocker G) x :=
      AiMathLab.P0054.G415.twoAvoidingRows_blockers_containing_card_ge_nine
        hGRows hBRows hAvoidCard
    have hDegreeCard : degree (blocker G) x ≤ (blocker G).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · let K := avoidPoint G x
    have hKClutter : IsClutter K := by
      simpa [K] using avoidPoint_isClutter hGClutter x
    have hKRows : RowsCardAtLeast K 3 := by
      intro E hEK
      exact hGRows E (mem_avoidPoint.mp (by simpa [K] using hEK)).1
    have hBKRows : RowsCardAtLeast (blocker K) 2 := by
      simpa [K] using blocker_avoidPoint_rows_cardAtLeast_two hBRows x
    have hSeven : 7 ≤ (blocker K).card :=
      threeRow_blocker_card_ge_seven hKClutter
        (by simpa [K] using hAvoidCard) hKRows hBKRows
    have hLift : (blocker K).card ≤ (blocker G).card := by
      simpa [K] using blocker_avoidPoint_card_le_blocker G x
    omega

end AiMathLab.P0054.MiddleNineDegree
