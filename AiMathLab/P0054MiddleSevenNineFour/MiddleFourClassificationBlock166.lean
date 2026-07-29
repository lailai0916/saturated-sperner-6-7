import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock165
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck563
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck564
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck565
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck566
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck567

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_166 (offset : Fin 64) :
    middleFourClassificationMaskCheck (10624 + offset.val) = true := by
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
      middle_four_classification_group_563 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_564 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_564 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_565 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_565 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_565 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_565 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_566 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_566 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_566 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_566 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_567 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_567 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_567 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_567 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_567 (by decide)
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
