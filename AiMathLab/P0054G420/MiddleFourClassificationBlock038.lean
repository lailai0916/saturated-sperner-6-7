import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck145
import AiMathLab.P0054G420.MiddleFourClassificationCheck146
import AiMathLab.P0054G420.MiddleFourClassificationCheck147
import AiMathLab.P0054G420.MiddleFourClassificationCheck148
import AiMathLab.P0054G420.MiddleFourClassificationCheck149
import AiMathLab.P0054G420.MiddleFourClassificationCheck150
import AiMathLab.P0054G420.MiddleFourClassificationCheck151
import AiMathLab.P0054G420.MiddleFourClassificationMask02470

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_038 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2432 + offset.val) = true := by
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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_145 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_146 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_146 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_146 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_147 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_147 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_147 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_148 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_148 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_148 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_149 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_150 (by decide)
  · exact middle_four_classification_mask_02470
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_150 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_150 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_150 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_150 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_150 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_150 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_151 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_151 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
