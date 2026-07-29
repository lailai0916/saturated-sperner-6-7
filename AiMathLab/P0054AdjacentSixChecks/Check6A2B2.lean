import AiMathLab.P0054AdjacentSixChecks.Check6A2B1

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check fixes loop digits (2, 2) for 6 low vertices.
theorem adjacent_six_check_six_a2b2 :
    adjacentSixCompactCheckAB 6 2 2 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
