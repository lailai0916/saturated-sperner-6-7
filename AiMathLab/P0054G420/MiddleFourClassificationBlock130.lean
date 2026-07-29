import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck320
import AiMathLab.P0054G420.MiddleFourClassificationCheck321
import AiMathLab.P0054G420.MiddleFourClassificationCheck322
import AiMathLab.P0054G420.MiddleFourClassificationCheck323
import AiMathLab.P0054G420.MiddleFourClassificationCheck324
import AiMathLab.P0054G420.MiddleFourClassificationCheck325
import AiMathLab.P0054G420.MiddleFourClassificationCheck326
import AiMathLab.P0054G420.MiddleFourClassificationCheck327
import AiMathLab.P0054G420.MiddleFourClassificationCheck328
import AiMathLab.P0054G420.MiddleFourClassificationCheck329
import AiMathLab.P0054G420.MiddleFourClassificationMask08331
import AiMathLab.P0054G420.MiddleFourClassificationMask08333
import AiMathLab.P0054G420.MiddleFourClassificationMask08339
import AiMathLab.P0054G420.MiddleFourClassificationMask08363

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_130 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8320 + offset.val) = true := by
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
  · exact middle_four_classification_mask_08331
  · rfl
  · exact middle_four_classification_mask_08333
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_320 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_08339
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_321 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_321 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_322 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_323 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_324 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_325 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_325 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_326 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_326 (by decide)
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
  · exact middle_four_classification_mask_08363
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_327 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_327 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_328 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_328 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_328 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_328 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_329 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_329 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_329 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_329 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_329 (by decide)
  · rfl

end AiMathLab.P0054.G420
