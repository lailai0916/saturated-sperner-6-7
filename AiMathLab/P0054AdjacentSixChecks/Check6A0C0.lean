import AiMathLab.P0054AdjacentSixChecks.Check6A0C0D2

namespace AiMathLab.P0054.AdjacentSixFinite

theorem adjacent_six_check_six_a0b0c0 :
    (List.range 3).all (fun d ↦ adjacentSixCompactSubcheck 6 0 0 0 d) = true := by
  apply List.all_eq_true.mpr
  intro d hd
  simp only [List.mem_range] at hd
  interval_cases d
  · exact adjacent_six_check_six_a0b0c0d0
  · exact adjacent_six_check_six_a0b0c0d1
  · exact adjacent_six_check_six_a0b0c0d2

end AiMathLab.P0054.AdjacentSixFinite
