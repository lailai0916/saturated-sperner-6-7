import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock193
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck589
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck590
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck591
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck592
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck593

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_194 (offset : Fin 64) :
    middleFourClassificationMaskCheck (12416 + offset.val) = true := by
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
      middle_four_classification_group_589 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_590 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_590 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_591 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_591 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_591 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_592 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_592 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_592 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_592 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_593 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_593 (by decide)
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
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
