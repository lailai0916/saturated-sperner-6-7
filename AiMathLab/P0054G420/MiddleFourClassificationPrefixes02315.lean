import AiMathLab.P0054G420.MiddleFourFinite

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The fixed prefix leaves a kernel-reducible residual multiplicity tree.
theorem middle_four_classification_prefixes_02315 :
    [[1, 1], [1, 2], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 2315) = true := by
  rfl

end AiMathLab.P0054.G420
