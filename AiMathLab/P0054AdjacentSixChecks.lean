import AiMathLab.P0054AdjacentSixChecks.Check6Done

namespace AiMathLab.P0054.AdjacentSixFinite

theorem adjacent_six_check_true {lowCount : Nat}
    (hLow : 1 ≤ lowCount) (hHigh : lowCount ≤ 6) :
    adjacentSixCompactCheck lowCount = true := by
  interval_cases lowCount
  · exact adjacent_six_check_one
  · exact adjacent_six_check_two
  · exact adjacent_six_check_three
  · exact adjacent_six_check_four
  · exact adjacent_six_check_five
  · exact adjacent_six_check_six

end AiMathLab.P0054.AdjacentSixFinite
