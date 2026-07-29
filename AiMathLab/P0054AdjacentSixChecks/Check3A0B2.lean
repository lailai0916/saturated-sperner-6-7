import AiMathLab.P0054AdjacentSixChecks.Check3A0B1

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check fixes loop digits (0, 2) for 3 low vertices.
theorem adjacent_six_check_three_a0b2 :
    adjacentSixCompactCheckAB 3 0 2 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
