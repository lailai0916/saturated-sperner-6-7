import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck272
import AiMathLab.P0054G420.MiddleFourClassificationCheck273
import AiMathLab.P0054G420.MiddleFourClassificationCheck274
import AiMathLab.P0054G420.MiddleFourClassificationCheck275
import AiMathLab.P0054G420.MiddleFourClassificationCheck276
import AiMathLab.P0054G420.MiddleFourClassificationCheck277
import AiMathLab.P0054G420.MiddleFourClassificationCheck278
import AiMathLab.P0054G420.MiddleFourClassificationCheck279

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_074 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4736 + offset.val) = true := by
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
      middle_four_classification_group_272 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_273 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_274 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_275 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_275 (by decide)
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
      middle_four_classification_group_275 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_275 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_276 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_276 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_276 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_277 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_277 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_277 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_277 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
