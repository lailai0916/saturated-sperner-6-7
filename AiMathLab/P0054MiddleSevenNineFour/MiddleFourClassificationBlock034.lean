import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock033
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck156
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck157
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck158
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck159
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck160
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck161
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck162
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck163
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck164
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck165
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck166
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02187
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02195
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02211

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_034 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2176 + offset.val) = true := by
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
  · exact middle_four_classification_mask_02187
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_156 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_02195
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_157 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_158 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_159 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_160 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_160 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_02211
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_161 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_162 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_163 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_164 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_164 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_164 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_165 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_165 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_165 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_165 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_165 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_166 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_166 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
