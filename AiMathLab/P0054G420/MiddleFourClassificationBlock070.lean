import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck253
import AiMathLab.P0054G420.MiddleFourClassificationCheck254
import AiMathLab.P0054G420.MiddleFourClassificationCheck255
import AiMathLab.P0054G420.MiddleFourClassificationCheck256
import AiMathLab.P0054G420.MiddleFourClassificationCheck257
import AiMathLab.P0054G420.MiddleFourClassificationCheck258
import AiMathLab.P0054G420.MiddleFourClassificationMask04491
import AiMathLab.P0054G420.MiddleFourClassificationMask04506

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_070 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4480 + offset.val) = true := by
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
  · exact middle_four_classification_mask_04491
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_253 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_253 (by decide)
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
  · exact middle_four_classification_mask_04506
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_254 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_255 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_256 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_256 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_256 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_257 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_257 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_257 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_257 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_257 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_258 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_258 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_258 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_258 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_258 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
