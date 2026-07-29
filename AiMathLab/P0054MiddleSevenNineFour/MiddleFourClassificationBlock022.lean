import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock021
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck123
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck124
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck125
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck126
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck127
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck128
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck129
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck130
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01419
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01422
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01449

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_022 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1408 + offset.val) = true := by
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
  · exact middle_four_classification_mask_01419
  · rfl
  · rfl
  · exact middle_four_classification_mask_01422
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_123 (by decide)
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
      middle_four_classification_group_124 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_125 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_125 (by decide)
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
  · exact middle_four_classification_mask_01449
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_125 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_126 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_126 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_126 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_126 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_127 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_128 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_128 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_129 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_129 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_129 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_129 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_129 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_130 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_130 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
