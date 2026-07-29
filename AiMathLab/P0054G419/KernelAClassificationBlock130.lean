import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck255
import AiMathLab.P0054G419.KernelAClassificationCheck256
import AiMathLab.P0054G419.KernelAClassificationCheck257
import AiMathLab.P0054G419.KernelAClassificationCheck258
import AiMathLab.P0054G419.KernelAClassificationCheck259
import AiMathLab.P0054G419.KernelAClassificationCheck260
import AiMathLab.P0054G419.KernelAClassificationCheck261
import AiMathLab.P0054G419.KernelAClassificationMask08331
import AiMathLab.P0054G419.KernelAClassificationMask08333
import AiMathLab.P0054G419.KernelAClassificationMask08339
import AiMathLab.P0054G419.KernelAClassificationMask08363

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_130 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (8320 + offset.val) = true := by
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
  · exact four_kernel_a_classification_mask_08331
  · rfl
  · exact four_kernel_a_classification_mask_08333
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_255 (by decide)
  · rfl
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_08339
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_256 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_256 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_257 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_257 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_258 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_259 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_259 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_260 (by decide)
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
  · exact four_kernel_a_classification_mask_08363
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_260 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_260 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_260 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_261 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_261 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_261 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_261 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G419
