import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock065
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck348
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck349
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck350
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck352
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck353
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck354
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck355
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck356
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck357
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck358
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck359
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck360
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04235
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04238
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04251
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04259

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_066 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4224 + offset.val) = true := by
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
  · exact middle_four_classification_mask_04235
  · rfl
  · rfl
  · exact middle_four_classification_mask_04238
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_348 (by decide)
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
  · exact middle_four_classification_mask_04251
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_349 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_350 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_04259
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_350 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_351 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_352 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_353 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_354 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_355 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_356 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_357 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_357 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_358 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_359 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_359 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_359 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_359 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_360 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_360 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_361 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_361 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
