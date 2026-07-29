import AiMathLab.P0054MiddleSevenNineK4Closed
import AiMathLab.P0054MiddleSevenNineSevenSideBasics

/-!
# Aggregation interface for the seven-plus-nine middle split

The three-row on the nine-row side is closed by the checked `K₄` extension
certificate.  The two remaining finite principles are stated explicitly:
the five-row rank-three certificate and the six-row residual coupling
certificate.  This keeps the global arbitrary-finite deduction independent
of their eventual chunk organization.
-/

namespace AiMathLab.P0054.MiddleSevenNineBridge

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.MiddleSevenNineDegree
open AiMathLab.P0054.MiddleSevenNineSevenSideBasics

def FiveRowRowsFourImpossiblePrinciple (alpha : Type*)
    [Fintype alpha] [DecidableEq alpha] : Prop :=
  ∀ {K : G413.Hypergraph alpha},
    IsClutter K →
    K.card = 5 →
    RowsCardAtLeast K 4 →
    (∀ R ∈ K, R.card ≤ 7) →
    RowsCardAtLeast (blocker K) 2 →
    MaxDegreeAtMost K 3 →
    (blocker K).card ≤ 7 →
    (pairRows (blocker K)).card ≤ 3 → False

def SixRowLowDegreeImpossiblePrinciple (alpha : Type*)
    [Fintype alpha] [DecidableEq alpha] : Prop :=
  ∀ {E : G413.Hypergraph alpha} {T : Row alpha},
    IsClutter E →
    E.card = 9 →
    RowsCardAtLeast E 4 →
    MaxDegreeAtMost E 4 →
    (blocker E).card = 7 →
    RowsCardAtLeast (blocker E) 3 →
    MaxDegreeAtMost (blocker E) 3 →
    T ∈ blocker E →
    T.card = 3 →
    (∀ x ∈ T, degree E x ≤ 3) → False

theorem threeRow_on_sevenSide_impossible_of_principles
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (hFive : FiveRowRowsFourImpossiblePrinciple alpha)
    (hSix : SixRowLowDegreeImpossiblePrinciple alpha)
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hHMax : MaxDegreeAtMost H 3)
    (hBCard : (blocker H).card = 9)
    (hBRowsFour : RowsCardAtLeast (blocker H) 4)
    (hBMax : MaxDegreeAtMost (blocker H) 4)
    {T : Row alpha} (hTH : T ∈ H) (hTCard : T.card = 3) : False := by
  classical
  have hDualCard : (blocker (blocker H)).card = 7 := by
    rw [blocker_involution hHClutter, hHCard]
  have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHRows
  have hDualMax : MaxDegreeAtMost (blocker (blocker H)) 3 := by
    simpa [blocker_involution hHClutter] using hHMax
  have hTBlocker : T ∈ blocker (blocker H) := by
    simpa [blocker_involution hHClutter] using hTH
  by_cases hDegreeFour : ∃ x ∈ T, degree (blocker H) x = 4
  · obtain ⟨x, _hxT, hxDegree⟩ := hDegreeFour
    let K := avoidPoint (blocker H) x
    have hData :
        IsClutter K ∧ K.card = 5 ∧ RowsCardAtLeast K 4 ∧
          (∀ R ∈ K, R.card ≤ 7) ∧
          RowsCardAtLeast (blocker K) 2 ∧ MaxDegreeAtMost K 3 ∧
          (blocker K).card ≤ 7 ∧
          (pairRows (blocker K)).card ≤ 3 := by
      simpa [K] using degreeFour_fiveKernel_data
        (blocker_isClutter H) hBCard hBRowsFour hBMax
          hDualCard hDualRows hDualMax hxDegree
    rcases hData with
      ⟨hKClutter, hKCard, hKRows, hKUpper, hBKRows,
        hKMax, hBKUpper, hPairUpper⟩
    exact hFive hKClutter hKCard hKRows hKUpper hBKRows
      hKMax hBKUpper hPairUpper
  · have hTLow : ∀ x ∈ T, degree (blocker H) x ≤ 3 := by
      intro x hxT
      have hxUpper := hBMax x
      have hxNotFour : degree (blocker H) x ≠ 4 := by
        intro hxDegree
        exact hDegreeFour ⟨x, hxT, hxDegree⟩
      omega
    exact hSix (blocker_isClutter H) hBCard hBRowsFour hBMax
      hDualCard hDualRows hDualMax hTBlocker hTCard hTLow

theorem sevenNine_impossible_of_principles
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (hFive : FiveRowRowsFourImpossiblePrinciple alpha)
    (hSix : SixRowLowDegreeImpossiblePrinciple alpha)
    {H : G413.Hypergraph alpha}
    (hHClutter : IsClutter H)
    (hHCard : H.card = 7)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3)
    (hBCard : (blocker H).card = 9) : False := by
  classical
  have hDegrees := middle_maxDegrees hHClutter hHCard hHRows hBRows hBCard
  by_cases hThreeBlocker : ∃ T ∈ blocker H, T.card = 3
  · obtain ⟨T, hTB, hTCard⟩ := hThreeBlocker
    exact AiMathLab.P0054.MiddleSevenNineK4.threeRow_on_nineSide_impossible
      hHClutter hHCard hHRows hDegrees.1 hBCard hBRows hDegrees.2
        hTB hTCard
  · have hBRowsFour : RowsCardAtLeast (blocker H) 4 := by
      intro E hEB
      have hLower := hBRows E hEB
      by_contra hNotFour
      have hECard : E.card = 3 := by omega
      exact hThreeBlocker ⟨E, hEB, hECard⟩
    have hThree := AiMathLab.P0054.G420.middle_has_three_row
      hHClutter (by omega) hHRows hBRows
    rcases hThree with ⟨T, hTH, hTCard⟩ | ⟨T, hTB, hTCard⟩
    · exact threeRow_on_sevenSide_impossible_of_principles
        hFive hSix hHClutter hHCard hHRows hDegrees.1 hBCard
          hBRowsFour hDegrees.2 hTH hTCard
    · exact hThreeBlocker ⟨T, hTB, hTCard⟩

end AiMathLab.P0054.MiddleSevenNineBridge
