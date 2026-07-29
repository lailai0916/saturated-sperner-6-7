import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_198 :
    [3009, 3010, 3011, 3016, 3017, 3018].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
