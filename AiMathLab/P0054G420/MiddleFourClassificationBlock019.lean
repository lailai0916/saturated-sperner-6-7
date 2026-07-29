import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck085
import AiMathLab.P0054G420.MiddleFourClassificationCheck086
import AiMathLab.P0054G420.MiddleFourClassificationCheck087
import AiMathLab.P0054G420.MiddleFourClassificationCheck088
import AiMathLab.P0054G420.MiddleFourClassificationMask01231

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_019 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1216 + offset.val) = true := by
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
      middle_four_classification_group_085 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_01231
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
      middle_four_classification_group_085 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_086 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_086 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_086 (by decide)
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
      middle_four_classification_group_086 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_087 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_087 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_087 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_087 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_087 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_087 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_088 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_088 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_088 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_088 (by decide)
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
