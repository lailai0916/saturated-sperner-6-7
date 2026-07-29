import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock025
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck132
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck133
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck134
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck135
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck136
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck137
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck138
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01675
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01677
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01690

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_026 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1664 + offset.val) = true := by
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
  · exact middle_four_classification_mask_01675
  · rfl
  · exact middle_four_classification_mask_01677
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_132 (by decide)
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
  · exact middle_four_classification_mask_01690
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_133 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_133 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_133 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_134 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_134 (by decide)
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
      middle_four_classification_group_134 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_135 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_135 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_135 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_136 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_136 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_137 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_137 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_137 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_137 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_137 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_137 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_138 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
