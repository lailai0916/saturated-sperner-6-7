import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck091
import AiMathLab.P0054G419.KernelAClassificationCheck092
import AiMathLab.P0054G419.KernelAClassificationCheck093
import AiMathLab.P0054G419.KernelAClassificationCheck094
import AiMathLab.P0054G419.KernelAClassificationCheck095
import AiMathLab.P0054G419.KernelAClassificationCheck096
import AiMathLab.P0054G419.KernelAClassificationCheck097
import AiMathLab.P0054G419.KernelAClassificationCheck098
import AiMathLab.P0054G419.KernelAClassificationMask02340
import AiMathLab.P0054G419.KernelAClassificationMask02341
import AiMathLab.P0054G419.KernelAClassificationMask02342
import AiMathLab.P0054G419.KernelAClassificationMask02348

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_036 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (2304 + offset.val) = true := by
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
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_091 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_092 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_092 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_092 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_093 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_093 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_093 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_094 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_094 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_095 (by decide)
  · exact four_kernel_a_classification_mask_02340
  · exact four_kernel_a_classification_mask_02341
  · exact four_kernel_a_classification_mask_02342
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_095 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_095 (by decide)
  · exact four_kernel_a_classification_mask_02348
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_096 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_097 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_097 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_097 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_097 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_098 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_098 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_098 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.G419
