import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock040
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck238
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck239
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck240
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck241
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck242
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck243
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck244
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck245
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck246
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck247
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck248
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck249
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck250
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck251
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck252
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck253

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_041 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2624 + offset.val) = true := by
  fin_cases offset
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_238 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_239 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_240 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_241 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_242 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_243 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_244 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_244 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_245 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_245 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_245 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_246 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_246 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_246 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_247 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_247 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_248 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_248 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_249 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_249 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_249 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_250 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_250 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_250 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_251 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_252 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_253 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
