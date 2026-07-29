import AiMathLab.P0054MiddleFourStrong
import AiMathLab.P0054MiddleFive
import AiMathLab.P0054G419
import AiMathLab.P0054G420

/-!
# The sixteen-member middle reduction

All cardinal splits except seven plus nine are discharged here.  The one
remaining split is an explicit theorem parameter, so the global aggregation
does not depend on the internal organization of its finite certificate.
-/

namespace AiMathLab.P0054.MiddleSixteenBridge

open AiMathLab.P0054.G413

theorem middle_sixteen_impossible_of_seven_nine
    {α : Type*} [Fintype α] [DecidableEq α]
    (hSevenNine : ∀ {K : G413.Hypergraph α},
      IsClutter K →
      K.card = 7 →
      RowsCardAtLeast K 3 →
      RowsCardAtLeast (blocker K) 3 →
      (blocker K).card = 9 → False)
    {H : G413.Hypergraph α}
    (hHClutter : IsClutter H)
    (hTotal : H.card + (blocker H).card = 16)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) : False := by
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
  have oriented_impossible {K : G413.Hypergraph α}
      (hKClutter : IsClutter K)
      (hKTotal : K.card + (blocker K).card = 16)
      (hKRows : RowsCardAtLeast K 3)
      (hBKRows : RowsCardAtLeast (blocker K) 3)
      (hKLower : 3 ≤ K.card)
      (hOrder : K.card ≤ (blocker K).card) : False := by
    have hKUpper : K.card ≤ 8 := by omega
    have hCases :
        K.card = 3 ∨ K.card = 4 ∨ K.card = 5 ∨
          K.card = 6 ∨ K.card = 7 ∨ K.card = 8 := by
      omega
    rcases hCases with hCard | hCard | hCard | hCard | hCard | hCard
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
    · have hBCard : (blocker K).card = 10 := by omega
      exact AiMathLab.P0054.G419.sixTen_impossible
        hKClutter hCard hKRows hBKRows hBCard
    · have hBCard : (blocker K).card = 9 := by omega
      exact hSevenNine hKClutter hCard hKRows hBKRows hBCard
    · have hBCard : (blocker K).card = 8 := by omega
      exact AiMathLab.P0054.G420.eightEight_impossible
        hKClutter hCard hKRows hBKRows hBCard
  by_cases hOrder : H.card ≤ (blocker H).card
  · exact oriented_impossible hHClutter hTotal hHRows hBRows hHLower hOrder
  · have hDualClutter : IsClutter (blocker H) := blocker_isClutter H
    have hDualTotal :
        (blocker H).card + (blocker (blocker H)).card = 16 := by
      rw [blocker_involution hHClutter]
      omega
    have hDualRows : RowsCardAtLeast (blocker (blocker H)) 3 := by
      simpa [blocker_involution hHClutter] using hHRows
    have hDualOrder :
        (blocker H).card ≤ (blocker (blocker H)).card := by
      rw [blocker_involution hHClutter]
      omega
    exact oriented_impossible hDualClutter hDualTotal hBRows hDualRows
      hBLower hDualOrder

end AiMathLab.P0054.MiddleSixteenBridge
