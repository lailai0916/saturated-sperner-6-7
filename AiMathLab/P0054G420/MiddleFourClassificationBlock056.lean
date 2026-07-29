import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck229
import AiMathLab.P0054G420.MiddleFourClassificationCheck230
import AiMathLab.P0054G420.MiddleFourClassificationCheck231
import AiMathLab.P0054G420.MiddleFourClassificationCheck232

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_056 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3584 + offset.val) = true := by
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
      middle_four_classification_group_229 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_229 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_229 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_230 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_230 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_230 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_230 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_231 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_231 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_231 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_231 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_231 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
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
