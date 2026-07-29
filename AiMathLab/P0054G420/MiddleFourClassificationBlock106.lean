import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck313
import AiMathLab.P0054G420.MiddleFourClassificationCheck314
import AiMathLab.P0054G420.MiddleFourClassificationCheck315
import AiMathLab.P0054G420.MiddleFourClassificationCheck316

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_106 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6784 + offset.val) = true := by
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
      middle_four_classification_group_313 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_314 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_314 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_314 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_314 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_315 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_315 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_315 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_315 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_315 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_316 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_316 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_316 (by decide)
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
