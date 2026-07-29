import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock066
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck362
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck363
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck364
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck365
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck366
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04315

namespace AiMathLab.P0054.MiddleSevenNineFinite

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
      middle_four_classification_group_362 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_363 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_363 (by decide)
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
  · exact middle_four_classification_mask_04315
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_363 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_363 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_364 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_364 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_364 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_364 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_365 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_365 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_365 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_365 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_366 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_366 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_366 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_366 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
