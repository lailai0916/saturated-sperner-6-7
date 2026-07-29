import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock057
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck340
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck343
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck344

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_058 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3712 + offset.val) = true := by
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
      middle_four_classification_group_340 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_340 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_340 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_341 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_341 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_342 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_342 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_342 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_343 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_343 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_343 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
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
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
