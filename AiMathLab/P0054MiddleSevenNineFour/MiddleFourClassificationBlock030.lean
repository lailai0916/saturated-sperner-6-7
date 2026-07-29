import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock029
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck150
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck151
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck152
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck153
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck154
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck155

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_030 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1920 + offset.val) = true := by
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
      middle_four_classification_group_150 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_151 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_152 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_153 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_153 (by decide)
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
      middle_four_classification_group_154 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
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
      middle_four_classification_group_154 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_155 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_155 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_155 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_155 (by decide)
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
