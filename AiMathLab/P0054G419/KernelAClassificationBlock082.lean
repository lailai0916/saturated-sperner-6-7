import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck226
import AiMathLab.P0054G419.KernelAClassificationCheck227
import AiMathLab.P0054G419.KernelAClassificationCheck228
import AiMathLab.P0054G419.KernelAClassificationCheck229
import AiMathLab.P0054G419.KernelAClassificationCheck230

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_082 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (5248 + offset.val) = true := by
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
      four_kernel_a_classification_group_226 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_227 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_227 (by decide)
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
      four_kernel_a_classification_group_227 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_227 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_228 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_228 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_229 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_229 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_229 (by decide)
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_229 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_230 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_230 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_230 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G419
