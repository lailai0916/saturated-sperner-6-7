import AiMathLab.P0054AdjacentSixChecks.Check5A1B1

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check fixes loop digits (1, 2) for 5 low vertices.
theorem adjacent_six_check_five_a1b2 :
    adjacentSixCompactCheckAB 5 1 2 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
