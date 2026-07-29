import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock041
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck254
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck255
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck256
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck257
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck258
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck259
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck260
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck261
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck262
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck263
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02709

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_042 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2688 + offset.val) = true := by
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
      middle_four_classification_group_254 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_255 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_255 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_256 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_257 (by decide)
  · exact middle_four_classification_mask_02709
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_258 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_258 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_259 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_259 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_259 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_260 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_260 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_261 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_261 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_262 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_262 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_263 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_263 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_263 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_263 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_263 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_263 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
