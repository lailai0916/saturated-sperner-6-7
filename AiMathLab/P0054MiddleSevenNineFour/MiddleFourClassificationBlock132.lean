import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock131
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck487
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck488
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck489
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck490
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck491
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck492
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck493
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck494
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck495
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck496
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck497
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck498
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck499
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck500
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck501
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck502
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08459
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08491

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_132 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8448 + offset.val) = true := by
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
  · exact middle_four_classification_mask_08459
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_487 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_488 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_489 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_490 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_491 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_492 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_492 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_492 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_493 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_493 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_494 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_495 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_496 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_496 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_496 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_496 (by decide)
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
  · exact middle_four_classification_mask_08491
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_497 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_497 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_498 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_499 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_499 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_500 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_500 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_500 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_501 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_501 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_502 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_502 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
