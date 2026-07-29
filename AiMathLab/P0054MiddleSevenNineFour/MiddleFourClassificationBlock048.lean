import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock047
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck291
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck292
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck293
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck294
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck295
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck296
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck297
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck298
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck299
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck300
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck301
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck302
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck303
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck304
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck305
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck306
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck307
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask03083
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask03087

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_048 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3072 + offset.val) = true := by
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
  · exact middle_four_classification_mask_03083
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_03087
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_291 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_292 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_293 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_294 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_295 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_296 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_297 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_297 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_298 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_299 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_300 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_301 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_302 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_303 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_304 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_304 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_304 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_306 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_306 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_306 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_306 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_306 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_306 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_307 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_307 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
