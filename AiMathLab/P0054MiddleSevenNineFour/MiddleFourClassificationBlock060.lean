import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock059
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck344
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck345
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck346

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_060 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3840 + offset.val) = true := by
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
      middle_four_classification_group_344 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
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
      middle_four_classification_group_345 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_346 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_346 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_346 (by decide)
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
