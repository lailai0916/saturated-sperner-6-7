import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock027
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck139
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck140
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck141
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck142
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck143
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck144
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck145
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck146
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck147
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01803

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_028 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1792 + offset.val) = true := by
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
  · exact middle_four_classification_mask_01803
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_139 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_140 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_141 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_142 (by decide)
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
      middle_four_classification_group_143 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_143 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_143 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_143 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_143 (by decide)
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
      middle_four_classification_group_144 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_145 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_145 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_146 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_146 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_147 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_147 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_147 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
