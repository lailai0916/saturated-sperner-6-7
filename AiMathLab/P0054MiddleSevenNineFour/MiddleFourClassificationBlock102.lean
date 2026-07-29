import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock101
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck446
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck447
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck448
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck449
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck450
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck451

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_102 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6528 + offset.val) = true := by
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
      middle_four_classification_group_446 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_447 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_447 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_447 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_448 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_448 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_449 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_449 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_450 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_450 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_450 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_450 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_450 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_450 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_451 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_451 (by decide)
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

end AiMathLab.P0054.MiddleSevenNineFinite
