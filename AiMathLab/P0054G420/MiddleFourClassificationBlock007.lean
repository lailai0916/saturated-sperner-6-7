import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck026
import AiMathLab.P0054G420.MiddleFourClassificationCheck027
import AiMathLab.P0054G420.MiddleFourClassificationCheck028
import AiMathLab.P0054G420.MiddleFourClassificationCheck029
import AiMathLab.P0054G420.MiddleFourClassificationCheck030
import AiMathLab.P0054G420.MiddleFourClassificationMask00458
import AiMathLab.P0054G420.MiddleFourClassificationMask00490

namespace AiMathLab.P0054.G420

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
      middle_four_classification_group_026 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_027 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_027 (by decide)
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
      middle_four_classification_group_028 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_028 (by decide)
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
  · exact middle_four_classification_mask_00490
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_029 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_029 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_029 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_029 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_029 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_030 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_030 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_030 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_030 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
