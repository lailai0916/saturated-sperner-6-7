import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck065
import AiMathLab.P0054G420.MiddleFourClassificationCheck066
import AiMathLab.P0054G420.MiddleFourClassificationCheck067
import AiMathLab.P0054G420.MiddleFourClassificationCheck068
import AiMathLab.P0054G420.MiddleFourClassificationCheck069
import AiMathLab.P0054G420.MiddleFourClassificationCheck070
import AiMathLab.P0054G420.MiddleFourClassificationMask00952

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_014 (offset : Fin 64) :
    middleFourClassificationMaskCheck (896 + offset.val) = true := by
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
      middle_four_classification_group_065 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_066 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_066 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_067 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_067 (by decide)
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
      middle_four_classification_group_067 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_068 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_068 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_068 (by decide)
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
      middle_four_classification_group_068 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_068 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_068 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_068 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_069 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_070 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_070 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_070 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_070 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00952
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_070 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_070 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
