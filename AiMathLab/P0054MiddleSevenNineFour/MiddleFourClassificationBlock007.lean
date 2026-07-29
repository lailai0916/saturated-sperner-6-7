import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock006
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck029
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck030
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck031
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck032
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck033
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck034
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck035
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck036
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00458
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00490

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_007 (offset : Fin 64) :
    middleFourClassificationMaskCheck (448 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00458
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_029 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_030 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_031 (by decide)
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
      middle_four_classification_group_032 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_033 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_033 (by decide)
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
  · exact middle_four_classification_mask_00490
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_033 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_034 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_034 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_034 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_034 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_035 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_035 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_035 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_035 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_035 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_036 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_036 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_036 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
