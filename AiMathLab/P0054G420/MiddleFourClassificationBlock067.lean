import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck248
import AiMathLab.P0054G420.MiddleFourClassificationCheck249
import AiMathLab.P0054G420.MiddleFourClassificationCheck250
import AiMathLab.P0054G420.MiddleFourClassificationCheck251
import AiMathLab.P0054G420.MiddleFourClassificationCheck252

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_067 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4288 + offset.val) = true := by
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
      middle_four_classification_group_248 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_248 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_249 (by decide)
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
      middle_four_classification_group_250 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
