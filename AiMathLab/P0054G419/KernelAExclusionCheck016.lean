import AiMathLab.P0054G419.KernelAExclusion

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The concrete vector expands a bounded compatibility search.
theorem four_kernel_a_exclusion_group_016 :
    fourKernelAExclusionCheck
      [0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0] = true := by
  rfl

end AiMathLab.P0054.G419
