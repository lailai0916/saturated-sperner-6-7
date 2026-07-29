import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_386 :
    [10510, 10511, 10514, 10515, 10516, 10518, 10522, 10523].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
