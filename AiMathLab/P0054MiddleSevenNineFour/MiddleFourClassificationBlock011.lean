import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock010
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck048
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck049
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck050
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck051
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck052
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck053
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck054
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00729

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_011 (offset : Fin 64) :
    middleFourClassificationMaskCheck (704 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00713
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_048 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_049 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_050 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00729
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_050 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_051 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_051 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_051 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_051 (by decide)
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
      middle_four_classification_group_052 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_053 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_053 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_053 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
