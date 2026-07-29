import AiMathLab.P0054G413.FiveRowLarge

namespace AiMathLab.P0054.G413

theorem residualLemma2_of_four_and_five_row_cases {α : Type*}
    [Fintype α]
    (hFour : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 4 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card)
    (hFive : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card) :
    ∀ R : Hypergraph α,
      IsClutter R →
      3 ≤ R.card →
      R.card ≤ 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  classical
  intro R hR hRlower hRupper hRRows hRPairs hBRows
  have hCases : R.card = 3 ∨ R.card = 4 ∨ R.card = 5 := by omega
  rcases hCases with hRcard | hRcard | hRcard
  · have hEight :=
      threeRow_blocker_card_ge_eight_of_rows_cardAtLeast_three hRcard hRRows hBRows
    omega
  · exact hFour R hR hRcard hRRows hRPairs hBRows
  · exact hFive R hR hRcard hRRows hRPairs hBRows

theorem fourRow_residual_bound_of_pair_case {α : Type*}
    [Fintype α]
    (hPairCase : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 4 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      (∃ E ∈ R, E.card = 2) →
      6 ≤ (blocker R).card) :
    ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 4 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  classical
  intro R hR hRcard hRRows hRPairs hBRows
  by_cases hPair : ∃ E ∈ R, E.card = 2
  · exact hPairCase R hR hRcard hRRows hRPairs hBRows hPair
  · have hLarge : RowsCardAtLeast R 3 := by
      intro E hER
      have hLower := hRRows E hER
      have hNotPair : E.card ≠ 2 := fun hEcard ↦ hPair ⟨E, hER, hEcard⟩
      omega
    have hNine := fourLargeRows_blocker_card_ge_nine hR hRcard hLarge hBRows
    omega

theorem fourRow_residual_bound {α : Type*}
    [Fintype α] :
    ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 4 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  exact fourRow_residual_bound_of_pair_case fourRow_pair_residual_bound

theorem fiveRow_residual_bound_of_large_case {α : Type*}
    [Fintype α]
    (hLarge : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card) :
    ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  classical
  intro R hR hRcard hRRows hRPairs hBRows
  by_cases hPair : ∃ E ∈ R, E.card = 2
  · exact fiveRow_pair_residual_bound R hR hRcard hRRows hRPairs hBRows hPair
  · have hLargeRows : RowsCardAtLeast R 3 := by
      intro E hER
      have hLower := hRRows E hER
      have hNotPair : E.card ≠ 2 := fun hEcard ↦ hPair ⟨E, hER, hEcard⟩
      omega
    exact hLarge R hR hRcard hLargeRows hBRows

theorem residualLemma2_of_five_large_row_case {α : Type*}
    [Fintype α]
    (hLarge : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card) :
    ∀ R : Hypergraph α,
      IsClutter R →
      3 ≤ R.card →
      R.card ≤ 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  exact residualLemma2_of_four_and_five_row_cases
    fourRow_residual_bound (fiveRow_residual_bound_of_large_case hLarge)

theorem residualLemma2_of_five_row_case {α : Type*}
    [Fintype α]
    (hFive : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card) :
    ∀ R : Hypergraph α,
      IsClutter R →
      3 ≤ R.card →
      R.card ≤ 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  exact residualLemma2_of_four_and_five_row_cases fourRow_residual_bound hFive

theorem residualLemma2_of_four_pair_and_five_row_cases {α : Type*}
    [Fintype α]
    (hFourPair : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 4 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      (∃ E ∈ R, E.card = 2) →
      6 ≤ (blocker R).card)
    (hFive : ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card) :
    ∀ R : Hypergraph α,
      IsClutter R →
      3 ≤ R.card →
      R.card ≤ 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  exact residualLemma2_of_four_and_five_row_cases
    (fourRow_residual_bound_of_pair_case hFourPair) hFive

theorem fiveRow_residual_bound {α : Type*}
    [Fintype α] :
    ∀ R : Hypergraph α,
      IsClutter R →
      R.card = 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  classical
  exact fiveRow_residual_bound_of_large_case fun R hR hRcard hRRows hBRows ↦
    fiveRow_large_residual_bound hR hRcard hRRows hBRows

theorem residualLemma2 {α : Type*}
    [Fintype α] :
    ∀ R : Hypergraph α,
      IsClutter R →
      3 ≤ R.card →
      R.card ≤ 5 →
      RowsCardAtLeast R 2 →
      (pairRows R).card ≤ 3 →
      RowsCardAtLeast (blocker R) 3 →
      6 ≤ (blocker R).card := by
  exact residualLemma2_of_four_and_five_row_cases
    fourRow_residual_bound fiveRow_residual_bound

end AiMathLab.P0054.G413
