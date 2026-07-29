import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck600
import AiMathLab.P0054MiddleSevenNineFourFinite

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_601 :
    [14859, 14881, 14889, 14987, 15009, 15017].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.MiddleSevenNineFinite
