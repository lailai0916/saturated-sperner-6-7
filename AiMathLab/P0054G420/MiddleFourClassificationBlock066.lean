import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck238
import AiMathLab.P0054G420.MiddleFourClassificationCheck239
import AiMathLab.P0054G420.MiddleFourClassificationCheck240
import AiMathLab.P0054G420.MiddleFourClassificationCheck241
import AiMathLab.P0054G420.MiddleFourClassificationCheck242
import AiMathLab.P0054G420.MiddleFourClassificationCheck243
import AiMathLab.P0054G420.MiddleFourClassificationCheck244
import AiMathLab.P0054G420.MiddleFourClassificationCheck245
import AiMathLab.P0054G420.MiddleFourClassificationCheck246
import AiMathLab.P0054G420.MiddleFourClassificationCheck247
import AiMathLab.P0054G420.MiddleFourClassificationMask04235
import AiMathLab.P0054G420.MiddleFourClassificationMask04238
import AiMathLab.P0054G420.MiddleFourClassificationMask04251
import AiMathLab.P0054G420.MiddleFourClassificationMask04259

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_066 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4224 + offset.val) = true := by
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
  · exact middle_four_classification_mask_04235
  · rfl
  · rfl
  · exact middle_four_classification_mask_04238
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_238 (by decide)
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
  · exact middle_four_classification_mask_04251
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_239 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_239 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_04259
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_240 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_240 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_241 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_241 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_242 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_243 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_244 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_245 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_245 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_246 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_246 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_246 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_247 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_247 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_247 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_247 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_247 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_247 (by decide)
  · rfl

end AiMathLab.P0054.G420
