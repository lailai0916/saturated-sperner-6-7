import AiMathLab.P0054AdjacentSixFinite

namespace AiMathLab.P0054.AdjacentSixFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This kernel check is the low-count-one slice of the pruned finite search.
theorem adjacent_six_check_one : adjacentSixCompactCheck 1 = true := by
  decide

end AiMathLab.P0054.AdjacentSixFinite
