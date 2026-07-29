import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck102
import AiMathLab.P0054G420.MiddleFourClassificationCheck103
import AiMathLab.P0054G420.MiddleFourClassificationCheck104
import AiMathLab.P0054G420.MiddleFourClassificationCheck105
import AiMathLab.P0054G420.MiddleFourClassificationCheck106
import AiMathLab.P0054G420.MiddleFourClassificationCheck107
import AiMathLab.P0054G420.MiddleFourClassificationMask01803

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_028 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1792 + offset.val) = true := by
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
  · exact middle_four_classification_mask_01803
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_102 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_103 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_104 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_104 (by decide)
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
      middle_four_classification_group_105 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_105 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_105 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_105 (by decide)
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
      middle_four_classification_group_105 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_105 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_105 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_105 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_105 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_106 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_106 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_106 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_107 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_107 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_107 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_107 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
