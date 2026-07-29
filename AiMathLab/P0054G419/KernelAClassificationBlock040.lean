import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck117
import AiMathLab.P0054G419.KernelAClassificationCheck118
import AiMathLab.P0054G419.KernelAClassificationCheck119
import AiMathLab.P0054G419.KernelAClassificationCheck120
import AiMathLab.P0054G419.KernelAClassificationCheck121
import AiMathLab.P0054G419.KernelAClassificationCheck122
import AiMathLab.P0054G419.KernelAClassificationCheck123
import AiMathLab.P0054G419.KernelAClassificationCheck124
import AiMathLab.P0054G419.KernelAClassificationCheck125
import AiMathLab.P0054G419.KernelAClassificationMask02580
import AiMathLab.P0054G419.KernelAClassificationMask02581
import AiMathLab.P0054G419.KernelAClassificationMask02582
import AiMathLab.P0054G419.KernelAClassificationMask02588

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_040 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (2560 + offset.val) = true := by
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
      four_kernel_a_classification_group_117 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_118 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_118 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_119 (by decide)
  · exact four_kernel_a_classification_mask_02580
  · exact four_kernel_a_classification_mask_02581
  · exact four_kernel_a_classification_mask_02582
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_119 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_119 (by decide)
  · exact four_kernel_a_classification_mask_02588
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_120 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_121 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_122 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_122 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_122 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_122 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_123 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_123 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_123 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_124 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_124 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_124 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_125 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_125 (by decide)
  · rfl

end AiMathLab.P0054.G419
