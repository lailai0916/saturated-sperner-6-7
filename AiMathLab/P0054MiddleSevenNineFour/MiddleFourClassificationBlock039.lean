import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock038
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck216
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck217
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck218
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck219
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck220

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_039 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2496 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_216 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_217 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_217 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_218 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_218 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_219 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_219 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_219 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_219 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_219 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
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
