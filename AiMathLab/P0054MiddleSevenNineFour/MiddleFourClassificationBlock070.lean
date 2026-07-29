import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock069
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck367
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck368
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck369
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck370
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck371
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck372
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck373
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck374
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04491
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04506
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04515

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_070 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4480 + offset.val) = true := by
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
  · exact middle_four_classification_mask_04491
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_367 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_368 (by decide)
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
  · exact middle_four_classification_mask_04506
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_369 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_370 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_04515
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_370 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_371 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_371 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_372 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_372 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_372 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_373 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_373 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_373 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_373 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_373 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_374 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_374 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_374 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_374 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
