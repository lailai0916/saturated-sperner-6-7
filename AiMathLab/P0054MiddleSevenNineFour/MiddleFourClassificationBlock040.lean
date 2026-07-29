import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock039
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck221
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck222
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck223
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck224
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck225
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck226
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck227
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck228
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck229
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck230
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck231
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck232
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck233
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck234
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck235
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck236
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck237
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02571
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02581
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02582
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02590

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_040 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2560 + offset.val) = true := by
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
  · exact middle_four_classification_mask_02571
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_221 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_222 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_223 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_223 (by decide)
  · exact middle_four_classification_mask_02581
  · exact middle_four_classification_mask_02582
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_224 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_225 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_226 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_227 (by decide)
  · exact middle_four_classification_mask_02590
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_227 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_228 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_228 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_229 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_229 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_230 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_231 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_232 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_233 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_233 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_234 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_234 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_235 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_235 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_236 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_236 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_237 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
