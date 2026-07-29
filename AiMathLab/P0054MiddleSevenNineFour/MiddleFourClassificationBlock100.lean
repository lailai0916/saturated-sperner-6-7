import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock099
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck436
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck437
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck438
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck439
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck440
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck441
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck442
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck443
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck444
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask06411

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_100 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6400 + offset.val) = true := by
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
  · exact middle_four_classification_mask_06411
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_436 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_436 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_437 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_438 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_438 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_438 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_439 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_440 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_440 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_441 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_441 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_441 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_441 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_442 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_442 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_442 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_443 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_443 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_443 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_443 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_443 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_444 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
