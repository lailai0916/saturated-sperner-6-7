import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock133
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck506
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck507
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck508
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck509
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck510
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck515

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_134 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8576 + offset.val) = true := by
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
      middle_four_classification_group_506 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_507 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_508 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_509 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_510 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_510 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_511 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_511 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_512 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_512 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_512 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_513 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_514 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_514 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_514 (by decide)
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
      middle_four_classification_group_514 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_514 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_515 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_515 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_515 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_515 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_515 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_515 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
