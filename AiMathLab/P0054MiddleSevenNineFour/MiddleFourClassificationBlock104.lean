import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock103
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck451
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck452
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck453
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck454
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck455

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_104 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6656 + offset.val) = true := by
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
      middle_four_classification_group_451 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_452 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_452 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_452 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_452 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_453 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_453 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_453 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_453 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_454 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_454 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_454 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_454 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_454 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_454 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_455 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_455 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_455 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_455 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_455 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
