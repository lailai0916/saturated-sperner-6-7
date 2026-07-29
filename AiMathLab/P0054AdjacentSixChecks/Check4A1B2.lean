import AiMathLab.P0054AdjacentSixChecks.Check4A1B1

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check fixes loop digits (1, 2) for 4 low vertices.
theorem adjacent_six_check_four_a1b2 :
    adjacentSixCompactCheckAB 4 1 2 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
