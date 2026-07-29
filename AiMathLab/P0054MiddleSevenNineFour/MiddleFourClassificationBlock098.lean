import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock097
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck428
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck429
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck430
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck431
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck432
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck433
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck434
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask06283
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask06291

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_098 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6272 + offset.val) = true := by
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
  · exact middle_four_classification_mask_06283
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_428 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_429 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_06291
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_429 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_429 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_430 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_431 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_431 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_431 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_432 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_432 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_432 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_432 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_433 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_433 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_434 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_434 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_434 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_434 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_434 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_434 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
