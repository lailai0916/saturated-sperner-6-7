import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck259
import AiMathLab.P0054G420.MiddleFourClassificationCheck260
import AiMathLab.P0054G420.MiddleFourClassificationCheck261
import AiMathLab.P0054G420.MiddleFourClassificationCheck262
import AiMathLab.P0054G420.MiddleFourClassificationCheck263
import AiMathLab.P0054G420.MiddleFourClassificationCheck264
import AiMathLab.P0054G420.MiddleFourClassificationCheck265
import AiMathLab.P0054G420.MiddleFourClassificationCheck266
import AiMathLab.P0054G420.MiddleFourClassificationCheck267
import AiMathLab.P0054G420.MiddleFourClassificationCheck268
import AiMathLab.P0054G420.MiddleFourClassificationCheck269
import AiMathLab.P0054G420.MiddleFourClassificationMask04619
import AiMathLab.P0054G420.MiddleFourClassificationMask04635

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_072 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4608 + offset.val) = true := by
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
  · exact middle_four_classification_mask_04619
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_259 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_260 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_260 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_261 (by decide)
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
  · exact middle_four_classification_mask_04635
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_261 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_262 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_262 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_262 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_263 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_263 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_264 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_264 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_264 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_264 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_265 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_266 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_266 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_266 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_267 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_267 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_267 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_267 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_268 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_268 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_268 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_268 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_269 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_269 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.G420
