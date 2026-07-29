import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck183
import AiMathLab.P0054G419.KernelAClassificationCheck184
import AiMathLab.P0054G419.KernelAClassificationCheck185
import AiMathLab.P0054G419.KernelAClassificationCheck186
import AiMathLab.P0054G419.KernelAClassificationCheck187
import AiMathLab.P0054G419.KernelAClassificationCheck188
import AiMathLab.P0054G419.KernelAClassificationCheck189
import AiMathLab.P0054G419.KernelAClassificationCheck190
import AiMathLab.P0054G419.KernelAClassificationMask04235
import AiMathLab.P0054G419.KernelAClassificationMask04238
import AiMathLab.P0054G419.KernelAClassificationMask04251
import AiMathLab.P0054G419.KernelAClassificationMask04259

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_066 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (4224 + offset.val) = true := by
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
  · exact four_kernel_a_classification_mask_04235
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_04238
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_183 (by decide)
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
  · exact four_kernel_a_classification_mask_04251
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_183 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_184 (by decide)
  · rfl
  · rfl
  · rfl
  · exact four_kernel_a_classification_mask_04259
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_184 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_185 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_186 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_186 (by decide)
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_187 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_188 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_188 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_189 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_189 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_189 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_189 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_190 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_190 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G419
