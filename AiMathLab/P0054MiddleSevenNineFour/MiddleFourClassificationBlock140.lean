import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock139
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck526
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck527
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck528
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck529
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck530
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck531

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_140 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8960 + offset.val) = true := by
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
      middle_four_classification_group_526 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_527 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_527 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_527 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_527 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_528 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_528 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_528 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_529 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_529 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_529 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_529 (by decide)
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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_529 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_530 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_530 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_530 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_530 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_530 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_531 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_531 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
