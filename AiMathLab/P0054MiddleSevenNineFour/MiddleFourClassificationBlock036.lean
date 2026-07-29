import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock035
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck174
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck175
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck176
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck177
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck178
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck179
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck180
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck181
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck182
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck183
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck184
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck185
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck186
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck187
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck188
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck189
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck190
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02349

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_036 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2304 + offset.val) = true := by
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
  · exact middle_four_classification_mask_02315
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_174 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_175 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_176 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_177 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_177 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_178 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_178 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_179 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_180 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_180 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_180 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_181 (by decide)
  · exact middle_four_classification_mask_02341
  · exact middle_four_classification_mask_02342
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_182 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_183 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_184 (by decide)
  · exact middle_four_classification_mask_02349
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_185 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_185 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_186 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_186 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_186 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_187 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_187 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_188 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_188 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_188 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_189 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_190 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_190 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
