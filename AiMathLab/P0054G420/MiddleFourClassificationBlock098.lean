import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck295
import AiMathLab.P0054G420.MiddleFourClassificationCheck296
import AiMathLab.P0054G420.MiddleFourClassificationCheck297
import AiMathLab.P0054G420.MiddleFourClassificationCheck298
import AiMathLab.P0054G420.MiddleFourClassificationCheck299
import AiMathLab.P0054G420.MiddleFourClassificationCheck300
import AiMathLab.P0054G420.MiddleFourClassificationMask06283
import AiMathLab.P0054G420.MiddleFourClassificationMask06291

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_098 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6272 + offset.val) = true := by
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
  · exact middle_four_classification_mask_06283
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_295 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_296 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_06291
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_296 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_296 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_297 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_297 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_298 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_298 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_298 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_299 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_299 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_299 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_299 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_300 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_300 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_300 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_300 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
