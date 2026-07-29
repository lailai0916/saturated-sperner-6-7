import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock013
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck087
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck088
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck089
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck090
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck091
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck092
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck093
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck094
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck095
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck096
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck097
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00952

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_014 (offset : Fin 64) :
    middleFourClassificationMaskCheck (896 + offset.val) = true := by
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
      middle_four_classification_group_087 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_088 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_089 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_090 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_091 (by decide)
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
      middle_four_classification_group_091 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_091 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_092 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_092 (by decide)
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
      middle_four_classification_group_092 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_092 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_093 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_093 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_094 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_095 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_096 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_096 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_096 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_096 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_097 (by decide)
  · rfl
  · exact middle_four_classification_mask_00952
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_097 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_097 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
