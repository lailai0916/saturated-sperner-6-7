import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock009
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck037
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck038
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck039
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck040
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck041
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck042
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck043
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck044
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck045
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck046
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck047
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00651
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00653
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00681

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_010 (offset : Fin 64) :
    middleFourClassificationMaskCheck (640 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00651
  · rfl
  · exact middle_four_classification_mask_00653
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_037 (by decide)
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
      middle_four_classification_group_038 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_039 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_040 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_041 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_041 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00681
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_042 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_042 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_043 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_043 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_044 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_044 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_044 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_045 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_045 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_046 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_046 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_046 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_047 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
