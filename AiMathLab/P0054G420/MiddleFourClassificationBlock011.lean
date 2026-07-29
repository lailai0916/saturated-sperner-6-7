import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck039
import AiMathLab.P0054G420.MiddleFourClassificationCheck040
import AiMathLab.P0054G420.MiddleFourClassificationCheck041
import AiMathLab.P0054G420.MiddleFourClassificationCheck042
import AiMathLab.P0054G420.MiddleFourClassificationCheck043
import AiMathLab.P0054G420.MiddleFourClassificationMask00713
import AiMathLab.P0054G420.MiddleFourClassificationMask00729

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_011 (offset : Fin 64) :
    middleFourClassificationMaskCheck (704 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00713
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_039 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_040 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_040 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00729
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_041 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_041 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_041 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_041 (by decide)
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
      middle_four_classification_group_042 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_042 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_042 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_043 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_043 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_043 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_043 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
