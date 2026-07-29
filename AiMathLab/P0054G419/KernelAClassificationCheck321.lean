import AiMathLab.P0054G419.KernelAFinite

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The bounded group is split so kernel reduction remains incremental.
theorem four_kernel_a_classification_group_321 :
    [10900, 10913, 10915, 10921].all fourKernelAClassificationMaskCheck = true := by
  rfl

end AiMathLab.P0054.G419
