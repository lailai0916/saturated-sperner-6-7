import AiMathLab.P0054G417.SupportMultigraphEarlyPrefix

namespace AiMathLab.P0054.G417

set_option linter.style.longLine false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- This bounded prefix leaves a kernel-reducible residual search.
theorem six_support_multigraph_early_prefix_check_5_3_2_3_2 :
    sixSupportMultigraphEarlyCheckValues 5 15 [3, 2, 3, 2] sixSupportOrder5 sixCompletionGroups5 0 sixCompactDegreesZero 0 = true := by
  rfl

end AiMathLab.P0054.G417
