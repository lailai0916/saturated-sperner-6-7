import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock001
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck000
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck001
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck002
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck003
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck004
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck005
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck006
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck007
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck008
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck009
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck010
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00139
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00143
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00155
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00158
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00171
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00173
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00179

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_002 (offset : Fin 64) :
    middleFourClassificationMaskCheck (128 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00139
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00143
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
  · exact middle_four_classification_mask_00155
  · rfl
  · rfl
  · exact middle_four_classification_mask_00158
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_000 (by decide)
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
  · exact middle_four_classification_mask_00171
  · rfl
  · exact middle_four_classification_mask_00173
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_001 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00179
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_002 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_003 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_004 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_005 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_006 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_007 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_008 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_009 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_010 (by decide)

end AiMathLab.P0054.MiddleSevenNineFinite
