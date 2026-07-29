import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock017
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck103
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck104
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck105
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck106
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck107
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck108
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck109
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck110
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck116
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck117
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01163
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01167
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01178
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask01193

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_018 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1152 + offset.val) = true := by
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
  · exact middle_four_classification_mask_01163
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_01167
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
  · exact middle_four_classification_mask_01178
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_103 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_104 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_105 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_01193
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_106 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_107 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_108 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_108 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_109 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_110 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_111 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_112 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_112 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_113 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_113 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_114 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_115 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_116 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_116 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_117 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_117 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_117 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
