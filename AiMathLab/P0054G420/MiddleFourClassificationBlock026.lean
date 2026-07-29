import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck096
import AiMathLab.P0054G420.MiddleFourClassificationCheck097
import AiMathLab.P0054G420.MiddleFourClassificationCheck098
import AiMathLab.P0054G420.MiddleFourClassificationCheck099
import AiMathLab.P0054G420.MiddleFourClassificationCheck100
import AiMathLab.P0054G420.MiddleFourClassificationCheck101
import AiMathLab.P0054G420.MiddleFourClassificationMask01675
import AiMathLab.P0054G420.MiddleFourClassificationMask01677

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_026 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1664 + offset.val) = true := by
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
  · exact middle_four_classification_mask_01675
  · rfl
  · exact middle_four_classification_mask_01677
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_096 (by decide)
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
      middle_four_classification_group_097 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_098 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_098 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_098 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_098 (by decide)
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
      middle_four_classification_group_099 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_099 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_099 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_100 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_100 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_100 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_100 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_100 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_101 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_101 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_101 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
