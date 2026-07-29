import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock034
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck167
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck168
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck169
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck170
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck171
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck172
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck173
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02243
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02247

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_035 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2240 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_02243
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_02247
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_167 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_168 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_169 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_169 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_170 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_170 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_170 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_171 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_171 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_172 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_172 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_172 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
