import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_300 :
    [6317, 6318, 6324, 6332, 6339, 6347].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
