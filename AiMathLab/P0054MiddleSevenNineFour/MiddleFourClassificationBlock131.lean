import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock130
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck482
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck483
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck484
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck485
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck486
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08427

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_131 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8384 + offset.val) = true := by
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
      middle_four_classification_group_482 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_483 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_483 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_483 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_483 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_484 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_484 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_484 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_485 (by decide)
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
  · exact middle_four_classification_mask_08427
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_485 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_485 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_485 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_486 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_486 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_486 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_486 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_486 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
