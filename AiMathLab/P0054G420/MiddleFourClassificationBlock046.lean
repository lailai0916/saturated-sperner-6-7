import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck193
import AiMathLab.P0054G420.MiddleFourClassificationCheck194
import AiMathLab.P0054G420.MiddleFourClassificationCheck195
import AiMathLab.P0054G420.MiddleFourClassificationCheck196
import AiMathLab.P0054G420.MiddleFourClassificationCheck197

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_046 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2944 + offset.val) = true := by
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
      middle_four_classification_group_193 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_194 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_194 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_194 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_194 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_195 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_195 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_195 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_195 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_196 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_196 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_196 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_197 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_197 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
