import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock012
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck072
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck073
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck074
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck075
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck076
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck077
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck078
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck079
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck080
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck081
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck082
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck083
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck084
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck085
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck086

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_013 (offset : Fin 64) :
    middleFourClassificationMaskCheck (832 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_073 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_074 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_075 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_076 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_076 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_077 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_077 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_078 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_079 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_079 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_080 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_080 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_080 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_080 (by decide)
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
      middle_four_classification_group_081 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_081 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_082 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_082 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_083 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_083 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_083 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_083 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_083 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_084 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_084 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_085 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_085 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_085 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_085 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_086 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_086 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_086 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_086 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_086 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
