import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck151
import AiMathLab.P0054G420.MiddleFourClassificationCheck152
import AiMathLab.P0054G420.MiddleFourClassificationCheck153
import AiMathLab.P0054G420.MiddleFourClassificationCheck154

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_039 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2496 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_151 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_152 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_152 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_152 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_153 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_153 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_153 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_153 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_153 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_153 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
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
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
