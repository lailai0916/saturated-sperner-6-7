import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock002
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck010
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck011
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck012
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck013
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck014
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck015
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck016
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck017
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00203
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00207
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00219
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00222
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00223
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00235
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00237
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00239
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00243
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00251

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_003 (offset : Fin 64) :
    middleFourClassificationMaskCheck (192 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00203
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00207
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
  · exact middle_four_classification_mask_00219
  · rfl
  · rfl
  · exact middle_four_classification_mask_00222
  · exact middle_four_classification_mask_00223
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
  · exact middle_four_classification_mask_00235
  · rfl
  · exact middle_four_classification_mask_00237
  · rfl
  · exact middle_four_classification_mask_00239
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00243
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_010 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_011 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_012 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_013 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00251
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_014 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_015 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_016 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_017 (by decide)

end AiMathLab.P0054.MiddleSevenNineFinite
