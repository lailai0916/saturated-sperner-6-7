import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock036
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck191
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck192
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck193
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck194
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck195
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck196
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck197
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck198
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck199
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck200
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck201
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck202
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck203
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck204
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck205

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_037 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2368 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_191 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_192 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_193 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_194 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_195 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_196 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_197 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_197 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_197 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_198 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_198 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_198 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_199 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_199 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_199 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_200 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_200 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_200 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_201 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_201 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_201 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_202 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_202 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_203 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_203 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_205 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_205 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_205 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
