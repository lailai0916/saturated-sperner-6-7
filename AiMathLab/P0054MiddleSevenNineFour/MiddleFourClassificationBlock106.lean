import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock105
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck456
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck457
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck458
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck459
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck460
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck461

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_106 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6784 + offset.val) = true := by
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
      middle_four_classification_group_456 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_457 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_457 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_458 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_458 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_458 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_459 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_459 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_459 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_459 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_460 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_460 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_460 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_460 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_461 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_461 (by decide)
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
