import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck166
import AiMathLab.P0054G420.MiddleFourClassificationCheck167
import AiMathLab.P0054G420.MiddleFourClassificationCheck168
import AiMathLab.P0054G420.MiddleFourClassificationCheck169
import AiMathLab.P0054G420.MiddleFourClassificationCheck170
import AiMathLab.P0054G420.MiddleFourClassificationCheck171
import AiMathLab.P0054G420.MiddleFourClassificationCheck172
import AiMathLab.P0054G420.MiddleFourClassificationCheck173
import AiMathLab.P0054G420.MiddleFourClassificationCheck174
import AiMathLab.P0054G420.MiddleFourClassificationCheck175

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_041 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2624 + offset.val) = true := by
  fin_cases offset
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_166 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_167 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_168 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_168 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_169 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_170 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_170 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_170 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_171 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_171 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_171 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_171 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_172 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_172 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_172 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_172 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_173 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_174 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_174 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_174 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_174 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_174 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_174 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_174 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_175 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_175 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_175 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_175 (by decide)
  · rfl

end AiMathLab.P0054.G420
