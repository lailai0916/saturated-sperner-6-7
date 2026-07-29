import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_387 :
    [10524, 10531, 10532, 10534, 10539, 10540].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
