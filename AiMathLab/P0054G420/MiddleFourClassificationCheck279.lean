import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_279 :
    [4785, 4787, 4788, 4793, 4809].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
