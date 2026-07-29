import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck120
import AiMathLab.P0054G420.MiddleFourClassificationCheck121
import AiMathLab.P0054G420.MiddleFourClassificationCheck122
import AiMathLab.P0054G420.MiddleFourClassificationCheck123
import AiMathLab.P0054G420.MiddleFourClassificationCheck124
import AiMathLab.P0054G420.MiddleFourClassificationMask02243
import AiMathLab.P0054G420.MiddleFourClassificationMask02247

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_035 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2240 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_02243
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_02247
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_120 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_121 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_121 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_121 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_122 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_122 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_122 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_123 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_123 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_123 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_124 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_124 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_124 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_124 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
