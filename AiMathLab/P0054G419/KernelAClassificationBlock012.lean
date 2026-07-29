import AiMathLab.P0054G419.KernelAFinite
import AiMathLab.P0054G419.KernelAClassificationCheck032
import AiMathLab.P0054G419.KernelAClassificationCheck033
import AiMathLab.P0054G419.KernelAClassificationCheck034
import AiMathLab.P0054G419.KernelAClassificationCheck035
import AiMathLab.P0054G419.KernelAClassificationCheck036
import AiMathLab.P0054G419.KernelAClassificationCheck037
import AiMathLab.P0054G419.KernelAClassificationCheck038
import AiMathLab.P0054G419.KernelAClassificationMask00779
import AiMathLab.P0054G419.KernelAClassificationMask00816
import AiMathLab.P0054G419.KernelAClassificationMask00817
import AiMathLab.P0054G419.KernelAClassificationMask00818
import AiMathLab.P0054G419.KernelAClassificationMask00824

namespace AiMathLab.P0054.G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem four_kernel_a_classification_block_012 (offset : Fin 64) :
    fourKernelAClassificationMaskCheck (768 + offset.val) = true := by
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
  · exact four_kernel_a_classification_mask_00779
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_032 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_032 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_033 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_033 (by decide)
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
      four_kernel_a_classification_group_034 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_034 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_034 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_034 (by decide)
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
      four_kernel_a_classification_group_035 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_035 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_035 (by decide)
  · rfl
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_035 (by decide)
  · rfl
  · exact four_kernel_a_classification_mask_00816
  · exact four_kernel_a_classification_mask_00817
  · exact four_kernel_a_classification_mask_00818
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_036 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_037 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_037 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_037 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_038 (by decide)
  · exact four_kernel_a_classification_mask_00824
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_038 (by decide)
  · exact fourKernelAClassificationMaskCheck_of_list
      four_kernel_a_classification_group_038 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G419
