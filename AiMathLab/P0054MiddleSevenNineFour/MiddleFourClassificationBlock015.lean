import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock014
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck098
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck099
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck100
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck101
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck102

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_015 (offset : Fin 64) :
    middleFourClassificationMaskCheck (960 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_098 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_099 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_100 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_100 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_100 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_101 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_101 (by decide)
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
      middle_four_classification_group_101 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_101 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_102 (by decide)
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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_102 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_102 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_102 (by decide)
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
