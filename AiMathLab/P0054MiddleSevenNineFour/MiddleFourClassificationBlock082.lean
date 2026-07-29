import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock081
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck417
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck418
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck419
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck420
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck421

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_082 (offset : Fin 64) :
    middleFourClassificationMaskCheck (5248 + offset.val) = true := by
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
      middle_four_classification_group_417 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_418 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_418 (by decide)
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
      middle_four_classification_group_418 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_419 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_419 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_420 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_420 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_420 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_421 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_421 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_421 (by decide)
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
