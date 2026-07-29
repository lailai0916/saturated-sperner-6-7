import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock005
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck018
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck019
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck020
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck021
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck022
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck023
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck024
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck025
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck026
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck027
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck028
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00395
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00398
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00410

namespace AiMathLab.P0054.MiddleSevenNineFinite

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
  · exact middle_four_classification_mask_00410
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_019 (by decide)
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
      middle_four_classification_group_020 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_021 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_022 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_023 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_023 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_024 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_025 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_025 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_026 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_026 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_026 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_027 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_027 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_027 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_028 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
