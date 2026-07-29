import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck133
import AiMathLab.P0054G419.KernelAClassificationCheck134
import AiMathLab.P0054G419.KernelAClassificationCheck135
import AiMathLab.P0054G419.KernelAClassificationCheck136
import AiMathLab.P0054G419.KernelAClassificationCheck137
import AiMathLab.P0054G419.KernelAClassificationCheck138

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_042 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (2688 + offset.val) = true := by
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
      four_kernel_a_classification_group_133 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_134 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_134 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_135 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_136 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_136 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_137 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_137 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_137 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_138 (by decide)
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

end AiMathLab.P0054.G419
