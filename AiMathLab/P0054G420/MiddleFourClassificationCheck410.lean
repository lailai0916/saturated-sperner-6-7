import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_410 :
    [14476, 14483, 14491, 14499, 14507, 14603, 14610].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
