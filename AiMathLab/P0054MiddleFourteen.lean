import AiMathLab.P0054MiddleFourStrong
import AiMathLab.P0054MiddleFive
import AiMathLab.P0054MiddleSixEight

/-!
# Cardinal reduction at middle total fourteen
-/

namespace AiMathLab.P0054.MiddleFourteen

open AiMathLab.P0054.G413

theorem middle_fourteen_cards_eq_seven {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hTotal : H.card + (blocker H).card = 14)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    H.card = 7 ∧ (blocker H).card = 7 := by
  have hHRowsNonempty : RowsNonempty H := by
    intro E hE
    exact Finset.card_pos.mp (by have := hHRows E hE; omega)
  have hBRowsNonempty : RowsNonempty (blocker H) := by
    intro E hE
    exact Finset.card_pos.mp (by have := hBRows E hE; omega)
  have hHNonempty : H.Nonempty := by
    have hDouble := blocker_nonempty hBRowsNonempty
    rwa [blocker_involution hHClutter] at hDouble
  have hBNonempty : (blocker H).Nonempty := blocker_nonempty hHRowsNonempty
  have hHLower : 3 ≤ H.card := by
    obtain ⟨T, hTB⟩ := hBNonempty
    exact (hBRows T hTB).trans
      (minimalTransversal_card_le_rows (mem_blocker.mp hTB))
  have hBLower : 3 ≤ (blocker H).card := by
    obtain ⟨E, hEH⟩ := hHNonempty
    have hEDouble : E ∈ blocker (blocker H) := by
      rw [blocker_involution hHClutter]
      exact hEH
    exact (hHRows E hEH).trans
      (minimalTransversal_card_le_rows (mem_blocker.mp hEDouble))
  have oriented_eq_seven {K : G413.Hypergraph α}
      (hKClutter : IsClutter K)
      (hKTotal : K.card + (blocker K).card = 14)
      (hKRows : RowsCardAtLeast K 3)
      (hBKRows : RowsCardAtLeast (blocker K) 3)
      (hKLower : 3 ≤ K.card)
      (hOrder : K.card ≤ (blocker K).card) :
      K.card = 7 ∧ (blocker K).card = 7 := by
    have hKUpper : K.card ≤ 7 := by omega
    have hCases :
        K.card = 3 ∨ K.card = 4 ∨ K.card = 5 ∨
          K.card = 6 ∨ K.card = 7 := by
      omega
    rcases hCases with hCard | hCard | hCard | hCard | hCard
    · have hLarge :=
        AiMathLab.P0054.MiddleLower.threeRow_blocker_card_ge_twentySeven
          hCard hKRows hBKRows
      omega
    · have hLarge :=
        AiMathLab.P0054.MiddleFourStrong.blocker_card_ge_fourteen
          hKClutter hCard hKRows hBKRows
      omega
    · have hLarge :=
        AiMathLab.P0054.MiddleFive.blocker_card_ge_twelve
          hKClutter hCard hKRows hBKRows
      omega
    · have hBCard : (blocker K).card = 8 := by omega
      exact (AiMathLab.P0054.MiddleSixEight.sixEight_impossible
        hKClutter hCard hKRows hBKRows hBCard).elim
    · exact ⟨hCard, by omega⟩
  by_cases hOrder : H.card ≤ (blocker H).card
  · exact oriented_eq_seven hHClutter hTotal hHRows hBRows hHLower hOrder
  · have hDualClutter : IsClutter (blocker H) := blocker_isClutter H
    have hDualTotal :
        (blocker H).card + (blocker (blocker H)).card = 14 := by
      rw [blocker_involution hHClutter]
      omega
    have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
      simpa [blocker_involution hHClutter] using hHRows
    have hDualOrder :
        (blocker H).card ≤ (blocker (blocker H)).card := by
      rw [blocker_involution hHClutter]
      omega
    have hDual := oriented_eq_seven hDualClutter hDualTotal hBRows
      hDualRows hBLower hDualOrder
    rw [blocker_involution hHClutter] at hDual
    exact ⟨hDual.2, hDual.1⟩

end AiMathLab.P0054.MiddleFourteen
