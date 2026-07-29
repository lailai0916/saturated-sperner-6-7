import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck000
import AiMathLab.P0054G419.KernelAClassificationCheck001
import AiMathLab.P0054G419.KernelAClassificationCheck002
import AiMathLab.P0054G419.KernelAClassificationCheck003
import AiMathLab.P0054G419.KernelAClassificationCheck004
import AiMathLab.P0054G419.KernelAClassificationCheck005
import AiMathLab.P0054G419.KernelAClassificationMask00139
import AiMathLab.P0054G419.KernelAClassificationMask00143
import AiMathLab.P0054G419.KernelAClassificationMask00155
import AiMathLab.P0054G419.KernelAClassificationMask00158
import AiMathLab.P0054G419.KernelAClassificationMask00171
import AiMathLab.P0054G419.KernelAClassificationMask00173
import AiMathLab.P0054G419.KernelAClassificationMask00179

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_002 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (128 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_00139
  · rfl
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_00143
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_00155
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_00158
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_000 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_00171
  · rfl
  · exact four_kernel_a_classification_mask_00173
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_001 (by decide)
  · rfl
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_00179
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_001 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_002 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_002 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_003 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_003 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_004 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_004 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_005 (by decide)
  · rfl

end AiMathLab.P0054.G419
