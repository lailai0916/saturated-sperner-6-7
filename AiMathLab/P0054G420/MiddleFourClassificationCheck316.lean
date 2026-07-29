import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_316 :
    [6820, 6825, 6828, 6924, 6930, 6932, 6933, 6945, 6960].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
