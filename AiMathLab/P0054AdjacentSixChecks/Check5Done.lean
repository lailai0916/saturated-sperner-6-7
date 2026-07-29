import AiMathLab.P0054AdjacentSixChecks.Check5A2B2

namespace AiMathLab.P0054.AdjacentSixFinite

theorem adjacent_six_check_five : adjacentSixCompactCheck 5 = true := by
  rw [adjacentSixCompactCheck]
  apply List.all_eq_true.mpr
  intro a ha
  rw [adjacentSixCompactCheckA]
  apply List.all_eq_true.mpr
  intro b hb
  simp only [List.mem_range] at ha hb
  interval_cases a <;> interval_cases b <;> simp only [
    adjacent_six_check_five_a0b0,
    adjacent_six_check_five_a0b1,
    adjacent_six_check_five_a0b2,
    adjacent_six_check_five_a1b0,
    adjacent_six_check_five_a1b1,
    adjacent_six_check_five_a1b2,
    adjacent_six_check_five_a2b0,
    adjacent_six_check_five_a2b1,
    adjacent_six_check_five_a2b2]

end AiMathLab.P0054.AdjacentSixFinite
