import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck071
import AiMathLab.P0054G419.KernelAClassificationCheck072
import AiMathLab.P0054G419.KernelAClassificationCheck073
import AiMathLab.P0054G419.KernelAClassificationCheck074
import AiMathLab.P0054G419.KernelAClassificationMask01675
import AiMathLab.P0054G419.KernelAClassificationMask01690

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_026 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (1664 + offset.val) = true := by
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
  · exact four_kernel_a_classification_mask_01675
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_071 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_072 (by decide)
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
  · exact four_kernel_a_classification_mask_01690
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_072 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_072 (by decide)
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
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_072 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_072 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_073 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_073 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_073 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_074 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_074 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G419
