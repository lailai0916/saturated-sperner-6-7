import AiMathLab.P0054AdjacentSixChecks.Check5A0C2

namespace AiMathLab.P0054.AdjacentSixFinite

theorem adjacent_six_check_five_a0b0 : adjacentSixCompactCheckAB 5 0 0 = true := by
  rw [adjacentSixCompactCheckAB]
  apply List.all_eq_true.mpr
  intro c hc
  simp only [List.mem_range] at hc
  interval_cases c
  · exact adjacent_six_check_five_a0b0c0
  · exact adjacent_six_check_five_a0b0c1
  · exact adjacent_six_check_five_a0b0c2

end AiMathLab.P0054.AdjacentSixFinite
