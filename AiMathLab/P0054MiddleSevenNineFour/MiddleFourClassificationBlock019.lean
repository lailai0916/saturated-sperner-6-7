import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock018
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck118
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck119
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck120
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01231

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_019 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1216 + offset.val) = true := by
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
      middle_four_classification_group_118 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_01231
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
      middle_four_classification_group_119 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_119 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_119 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_120 (by decide)
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
      middle_four_classification_group_120 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_120 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_121 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_121 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_121 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_121 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_121 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_122 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_122 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_122 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_122 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_122 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
