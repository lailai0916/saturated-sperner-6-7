import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck301
import AiMathLab.P0054G420.MiddleFourClassificationCheck302
import AiMathLab.P0054G420.MiddleFourClassificationCheck303
import AiMathLab.P0054G420.MiddleFourClassificationCheck304
import AiMathLab.P0054G420.MiddleFourClassificationCheck305
import AiMathLab.P0054G420.MiddleFourClassificationCheck306
import AiMathLab.P0054G420.MiddleFourClassificationMask06411

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_100 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6400 + offset.val) = true := by
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
  · exact middle_four_classification_mask_06411
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_301 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_301 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_301 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_302 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_302 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_302 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_303 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_303 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_304 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_304 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_304 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_304 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_304 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_305 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_306 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.G420
