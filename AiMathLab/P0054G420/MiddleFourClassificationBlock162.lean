import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck379
import AiMathLab.P0054G420.MiddleFourClassificationCheck380
import AiMathLab.P0054G420.MiddleFourClassificationCheck381
import AiMathLab.P0054G420.MiddleFourClassificationCheck382
import AiMathLab.P0054G420.MiddleFourClassificationCheck383
import AiMathLab.P0054G420.MiddleFourClassificationMask10379
import AiMathLab.P0054G420.MiddleFourClassificationMask10403

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_162 (offset : Fin 64) :
    middleFourClassificationMaskCheck (10368 + offset.val) = true := by
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
  · exact middle_four_classification_mask_10379
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_379 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_380 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_380 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_380 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_381 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_381 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_381 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_381 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_382 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_382 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_382 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_10403
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_382 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_383 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_383 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_383 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_383 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_383 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
