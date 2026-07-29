import AiMathLab.P0054AdjacentSixChecks.Check4A1B2

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check fixes loop digits (2, 0) for 4 low vertices.
theorem adjacent_six_check_four_a2b0 :
    adjacentSixCompactCheckAB 4 2 0 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
