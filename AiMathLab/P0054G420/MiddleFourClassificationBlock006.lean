import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck018
import AiMathLab.P0054G420.MiddleFourClassificationCheck019
import AiMathLab.P0054G420.MiddleFourClassificationCheck020
import AiMathLab.P0054G420.MiddleFourClassificationCheck021
import AiMathLab.P0054G420.MiddleFourClassificationCheck022
import AiMathLab.P0054G420.MiddleFourClassificationCheck023
import AiMathLab.P0054G420.MiddleFourClassificationCheck024
import AiMathLab.P0054G420.MiddleFourClassificationCheck025
import AiMathLab.P0054G420.MiddleFourClassificationMask00395
import AiMathLab.P0054G420.MiddleFourClassificationMask00398

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_006 (offset : Fin 64) :
    middleFourClassificationMaskCheck (384 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00395
  · rfl
  · rfl
  · exact middle_four_classification_mask_00398
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_018 (by decide)
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
      middle_four_classification_group_019 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_020 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_020 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_020 (by decide)
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
      middle_four_classification_group_021 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_021 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_022 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_022 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_022 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_023 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_023 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_024 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_024 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_024 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_024 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_024 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_025 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_025 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_025 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.G420
