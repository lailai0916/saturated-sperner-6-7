import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck349
import AiMathLab.P0054G420.MiddleFourClassificationCheck350
import AiMathLab.P0054G420.MiddleFourClassificationCheck351
import AiMathLab.P0054G420.MiddleFourClassificationCheck352
import AiMathLab.P0054G420.MiddleFourClassificationCheck353
import AiMathLab.P0054G420.MiddleFourClassificationCheck354
import AiMathLab.P0054G420.MiddleFourClassificationCheck355
import AiMathLab.P0054G420.MiddleFourClassificationCheck356

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_134 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8576 + offset.val) = true := by
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
      middle_four_classification_group_349 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_350 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_350 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_351 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_351 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_352 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_352 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_353 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_353 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_353 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_353 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_354 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_354 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_354 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_354 (by decide)
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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_355 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_355 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_355 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_355 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_355 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_355 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_356 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_356 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
