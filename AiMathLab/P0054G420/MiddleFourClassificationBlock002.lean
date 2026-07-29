import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck000
import AiMathLab.P0054G420.MiddleFourClassificationCheck001
import AiMathLab.P0054G420.MiddleFourClassificationCheck002
import AiMathLab.P0054G420.MiddleFourClassificationCheck003
import AiMathLab.P0054G420.MiddleFourClassificationCheck004
import AiMathLab.P0054G420.MiddleFourClassificationCheck005
import AiMathLab.P0054G420.MiddleFourClassificationCheck006
import AiMathLab.P0054G420.MiddleFourClassificationCheck007
import AiMathLab.P0054G420.MiddleFourClassificationCheck008
import AiMathLab.P0054G420.MiddleFourClassificationMask00139
import AiMathLab.P0054G420.MiddleFourClassificationMask00143
import AiMathLab.P0054G420.MiddleFourClassificationMask00155
import AiMathLab.P0054G420.MiddleFourClassificationMask00158
import AiMathLab.P0054G420.MiddleFourClassificationMask00171
import AiMathLab.P0054G420.MiddleFourClassificationMask00173
import AiMathLab.P0054G420.MiddleFourClassificationMask00179

namespace AiMathLab.P0054.G420

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
      middle_four_classification_group_002 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_003 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_004 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_005 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_006 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_007 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_008 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_008 (by decide)

end AiMathLab.P0054.G420
