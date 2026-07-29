import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck190
import AiMathLab.P0054G420.MiddleFourClassificationCheck191
import AiMathLab.P0054G420.MiddleFourClassificationCheck192
import AiMathLab.P0054G420.MiddleFourClassificationCheck193

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_045 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2880 + offset.val) = true := by
  fin_cases offset
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_190 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_190 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_191 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_191 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_191 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_191 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_191 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_191 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
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
  · rfl
  · rfl

end AiMathLab.P0054.G420
