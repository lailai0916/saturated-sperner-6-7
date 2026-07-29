import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group keeps kernel reduction below the per-module cost limit.
theorem middle_four_classification_group_144 :
    [2413, 2414, 2418, 2420, 2421, 2426].all middleFourClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G420
