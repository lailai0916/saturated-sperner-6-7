import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck335
import AiMathLab.P0054G420.MiddleFourClassificationCheck336
import AiMathLab.P0054G420.MiddleFourClassificationCheck337
import AiMathLab.P0054G420.MiddleFourClassificationCheck338
import AiMathLab.P0054G420.MiddleFourClassificationCheck339
import AiMathLab.P0054G420.MiddleFourClassificationCheck340
import AiMathLab.P0054G420.MiddleFourClassificationCheck341
import AiMathLab.P0054G420.MiddleFourClassificationCheck342
import AiMathLab.P0054G420.MiddleFourClassificationCheck343
import AiMathLab.P0054G420.MiddleFourClassificationCheck344
import AiMathLab.P0054G420.MiddleFourClassificationCheck345
import AiMathLab.P0054G420.MiddleFourClassificationMask08459
import AiMathLab.P0054G420.MiddleFourClassificationMask08491

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_132 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8448 + offset.val) = true := by
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
  · exact middle_four_classification_mask_08459
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_335 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_335 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_336 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_337 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_337 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_339 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_339 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_340 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_341 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_341 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_341 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_342 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_342 (by decide)
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
  · exact middle_four_classification_mask_08491
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_342 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_342 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_343 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_343 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_344 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_345 (by decide)
  · rfl

end AiMathLab.P0054.G420
