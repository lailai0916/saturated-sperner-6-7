import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock129
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck468
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck469
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck470
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck471
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck472
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck473
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck474
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck475
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck476
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck477
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck478
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck479
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck480
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck481
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08339
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08363

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_130 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8320 + offset.val) = true := by
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
  · exact middle_four_classification_mask_08331
  · rfl
  · exact middle_four_classification_mask_08333
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_468 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_08339
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_469 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_469 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_470 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_471 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_472 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_473 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_474 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_475 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_476 (by decide)
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
  · exact middle_four_classification_mask_08363
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_476 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_477 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_478 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_478 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_479 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_479 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_479 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_480 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_480 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_480 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_481 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
