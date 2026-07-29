import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck108
import AiMathLab.P0054G419.KernelAClassificationCheck109
import AiMathLab.P0054G419.KernelAClassificationCheck110
import AiMathLab.P0054G419.KernelAClassificationCheck111
import AiMathLab.P0054G419.KernelAClassificationCheck112
import AiMathLab.P0054G419.KernelAClassificationCheck113

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_038 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (2432 + offset.val) = true := by
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
      four_kernel_a_classification_group_108 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_108 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_109 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_109 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_109 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_110 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_111 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_112 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_112 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_113 (by decide)
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
