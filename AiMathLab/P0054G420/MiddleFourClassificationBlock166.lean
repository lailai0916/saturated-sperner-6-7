import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck388
import AiMathLab.P0054G420.MiddleFourClassificationCheck389
import AiMathLab.P0054G420.MiddleFourClassificationCheck390
import AiMathLab.P0054G420.MiddleFourClassificationCheck391

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_166 (offset : Fin 64) :
    middleFourClassificationMaskCheck (10624 + offset.val) = true := by
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
      middle_four_classification_group_388 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_389 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_389 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_389 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_389 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_389 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_390 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_390 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_390 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_390 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_390 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_391 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_391 (by decide)
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

end AiMathLab.P0054.G420
