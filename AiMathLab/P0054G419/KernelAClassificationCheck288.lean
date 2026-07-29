import AiMathLab.P0054G419.KernelAFinite

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group is split so kernel reduction remains incremental.
theorem four_kernel_a_classification_group_288 :
    [8875, 8881, 8905, 8907].all fourKernelAClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G419
