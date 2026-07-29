import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck176
import AiMathLab.P0054G420.MiddleFourClassificationCheck177
import AiMathLab.P0054G420.MiddleFourClassificationCheck178
import AiMathLab.P0054G420.MiddleFourClassificationCheck179
import AiMathLab.P0054G420.MiddleFourClassificationCheck180
import AiMathLab.P0054G420.MiddleFourClassificationCheck181
import AiMathLab.P0054G420.MiddleFourClassificationMask02709

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_042 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2688 + offset.val) = true := by
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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_176 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_177 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_177 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_177 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_178 (by decide)
  · exact middle_four_classification_mask_02709
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_179 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_179 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_179 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_179 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_179 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_179 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_180 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_180 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_180 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_181 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_181 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_181 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_181 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_181 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_181 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
