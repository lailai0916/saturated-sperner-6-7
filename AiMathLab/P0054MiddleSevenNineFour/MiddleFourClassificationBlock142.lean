import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock141
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck532
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck533
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck534
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck535
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck536
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck537

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_142 (offset : Fin 64) :
    middleFourClassificationMaskCheck (9088 + offset.val) = true := by
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
      middle_four_classification_group_532 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_532 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_533 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_533 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_534 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_534 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_535 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_535 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_535 (by decide)
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
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_535 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_535 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_535 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_536 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_536 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_536 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_537 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
