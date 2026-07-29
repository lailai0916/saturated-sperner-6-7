import AiMathLab.P0054AdjacentSixChecks.Check3

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check fixes loop digits (0, 1) for 3 low vertices.
theorem adjacent_six_check_three_a0b1 :
    adjacentSixCompactCheckAB 3 0 1 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
