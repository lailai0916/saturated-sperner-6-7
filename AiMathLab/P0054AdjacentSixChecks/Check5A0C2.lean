import AiMathLab.P0054AdjacentSixChecks.Check5A0C2D2

namespace AiMathLab.P0054.AdjacentSixFinite

theorem adjacent_six_check_five_a0b0c2 :
    (List.range 3).all (fun d ↦ adjacentSixCompactSubcheck 5 0 0 2 d) = true := by
  apply List.all_eq_true.mpr
  intro d hd
  simp only [List.mem_range] at hd
  interval_cases d
  · exact adjacent_six_check_five_a0b0c2d0
  · exact adjacent_six_check_five_a0b0c2d1
  · exact adjacent_six_check_five_a0b0c2d2

end AiMathLab.P0054.AdjacentSixFinite
