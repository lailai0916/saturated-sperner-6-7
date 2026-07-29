import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck199
import AiMathLab.P0054G420.MiddleFourClassificationCheck200
import AiMathLab.P0054G420.MiddleFourClassificationCheck201
import AiMathLab.P0054G420.MiddleFourClassificationCheck202
import AiMathLab.P0054G420.MiddleFourClassificationCheck203
import AiMathLab.P0054G420.MiddleFourClassificationCheck204
import AiMathLab.P0054G420.MiddleFourClassificationCheck205
import AiMathLab.P0054G420.MiddleFourClassificationCheck206
import AiMathLab.P0054G420.MiddleFourClassificationCheck207
import AiMathLab.P0054G420.MiddleFourClassificationCheck208
import AiMathLab.P0054G420.MiddleFourClassificationCheck209
import AiMathLab.P0054G420.MiddleFourClassificationCheck210
import AiMathLab.P0054G420.MiddleFourClassificationCheck211
import AiMathLab.P0054G420.MiddleFourClassificationMask03083
import AiMathLab.P0054G420.MiddleFourClassificationMask03087

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_048 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3072 + offset.val) = true := by
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
  · exact middle_four_classification_mask_03083
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_03087
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_199 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_200 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_201 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_201 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_202 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_203 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_203 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_204 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_205 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_206 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_206 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_207 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_208 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_208 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_209 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_209 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_209 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_211 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_211 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_211 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
