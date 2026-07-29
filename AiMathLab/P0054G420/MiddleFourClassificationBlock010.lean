import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck031
import AiMathLab.P0054G420.MiddleFourClassificationCheck032
import AiMathLab.P0054G420.MiddleFourClassificationCheck033
import AiMathLab.P0054G420.MiddleFourClassificationCheck034
import AiMathLab.P0054G420.MiddleFourClassificationCheck035
import AiMathLab.P0054G420.MiddleFourClassificationCheck036
import AiMathLab.P0054G420.MiddleFourClassificationCheck037
import AiMathLab.P0054G420.MiddleFourClassificationCheck038
import AiMathLab.P0054G420.MiddleFourClassificationMask00651
import AiMathLab.P0054G420.MiddleFourClassificationMask00653

namespace AiMathLab.P0054.G420

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
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_032 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_032 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_033 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_033 (by decide)
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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_034 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_035 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_035 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_035 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_036 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_036 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_037 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_037 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_037 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_037 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_037 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_038 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_038 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_038 (by decide)
  · rfl

end AiMathLab.P0054.G420
