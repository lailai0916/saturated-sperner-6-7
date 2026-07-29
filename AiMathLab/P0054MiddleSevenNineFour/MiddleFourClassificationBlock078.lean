import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock077
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck412
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck413
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck414
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck415
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck416
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck417

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_078 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4992 + offset.val) = true := by
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
      middle_four_classification_group_412 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_413 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_413 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_413 (by decide)
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
      middle_four_classification_group_414 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_414 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_414 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_414 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_415 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_415 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_415 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_415 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_416 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_416 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_416 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_417 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
