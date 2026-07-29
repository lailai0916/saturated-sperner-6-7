import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck009
import AiMathLab.P0054G420.MiddleFourClassificationCheck010
import AiMathLab.P0054G420.MiddleFourClassificationCheck011
import AiMathLab.P0054G420.MiddleFourClassificationCheck012
import AiMathLab.P0054G420.MiddleFourClassificationCheck013
import AiMathLab.P0054G420.MiddleFourClassificationCheck014
import AiMathLab.P0054G420.MiddleFourClassificationCheck015
import AiMathLab.P0054G420.MiddleFourClassificationCheck016
import AiMathLab.P0054G420.MiddleFourClassificationCheck017
import AiMathLab.P0054G420.MiddleFourClassificationCheck018
import AiMathLab.P0054G420.MiddleFourClassificationMask00203
import AiMathLab.P0054G420.MiddleFourClassificationMask00207
import AiMathLab.P0054G420.MiddleFourClassificationMask00219
import AiMathLab.P0054G420.MiddleFourClassificationMask00222
import AiMathLab.P0054G420.MiddleFourClassificationMask00235
import AiMathLab.P0054G420.MiddleFourClassificationMask00237
import AiMathLab.P0054G420.MiddleFourClassificationMask00243

namespace AiMathLab.P0054.G420

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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_009 (by decide)
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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_010 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_00243
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_011 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_012 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_013 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_014 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_015 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_016 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_017 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_017 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_018 (by decide)

end AiMathLab.P0054.G420
