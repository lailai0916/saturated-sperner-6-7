import AiMathLab.P0054MiddleLower

/-!
# The five-row middle endpoint

Five rows of size at least three whose blocker rows also have size at least
three have at least eleven blockers; the already certified exact-eleven
exclusion raises this to twelve.
-/

namespace AiMathLab.P0054.MiddleFive

open AiMathLab.P0054.G413

theorem blocker_card_ge_eleven {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHCard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    11 ≤ (blocker H).card := by
  have hDegreeUpper := fiveRow_maxDegreeAtMost_three hHCard hHRows hBRows
  by_cases hLow : MaxDegreeAtMost H 2
  · exact (AiMathLab.P0054.G416.fiveRow_lowDegree_blocker_card_ge_fifteen
      hHCard hHRows hLow).trans' (by omega)
  · unfold MaxDegreeAtMost at hLow
    push Not at hLow
    obtain ⟨x, hx⟩ := hLow
    have hDegree : degree H x = 3 := by
      have := hDegreeUpper x
      omega
    have hContaining :=
      AiMathLab.P0054.G415.degreeThree_blockers_containing_card_ge_nine
        hHCard hHRows hBRows hDegree
    have hHNonempty : H.Nonempty := Finset.card_pos.mp (by omega)
    have hAvoiding := MiddleLower.avoid_blocker_card_ge_two
      hHNonempty hHRows x
    have hPartition := card_avoidPoint_add_degree (blocker H) x
    omega

theorem blocker_card_ge_twelve {α : Type*}
    [Fintype α] [DecidableEq α]
    {H : G413.Hypergraph α} (hHClutter : IsClutter H)
    (hHCard : H.card = 5)
    (hHRows : RowsCardAtLeast H 3)
    (hBRows : RowsCardAtLeast (blocker H) 3) :
    12 ≤ (blocker H).card := by
  have hEleven := blocker_card_ge_eleven hHCard hHRows hBRows
  by_contra hNot
  have hExact : (blocker H).card = 11 := by omega
  exact AiMathLab.P0054.G416.fiveEleven_impossible
    hHClutter hHCard hHRows hBRows hExact

end AiMathLab.P0054.MiddleFive
