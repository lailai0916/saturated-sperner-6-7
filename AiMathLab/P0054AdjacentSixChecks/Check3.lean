import AiMathLab.P0054AdjacentSixChecks.Check2

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check fixes the first two loop digits in the low-count-three slice.
theorem adjacent_six_check_three_a0b0 : adjacentSixCompactCheckAB 3 0 0 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
