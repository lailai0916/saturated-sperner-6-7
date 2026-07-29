import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck280
import AiMathLab.P0054G420.MiddleFourClassificationCheck281
import AiMathLab.P0054G420.MiddleFourClassificationCheck282
import AiMathLab.P0054G420.MiddleFourClassificationCheck283

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_076 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4864 + offset.val) = true := by
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
      middle_four_classification_group_280 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
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
      middle_four_classification_group_281 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_283 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_283 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_283 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
