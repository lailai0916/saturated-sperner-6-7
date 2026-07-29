import AiMathLab.P0054AdjacentSixChecks.Check1

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check is the low-count-two slice of the pruned finite search.
theorem adjacent_six_check_two : adjacentSixCompactCheck 2 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
