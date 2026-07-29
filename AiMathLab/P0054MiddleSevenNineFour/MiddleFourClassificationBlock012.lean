import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock011
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck055
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck056
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck057
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck058
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck059
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck060
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck061
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck062
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck063
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck064
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck065
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck066
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck067
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck068
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck069
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck070
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck071
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck072
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00779
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00817
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00819
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask00824

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_012 (offset : Fin 64) :
    middleFourClassificationMaskCheck (768 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00779
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_055 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_056 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_057 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_058 (by decide)
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
      middle_four_classification_group_059 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_060 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_060 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_061 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_061 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_061 (by decide)
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
      middle_four_classification_group_062 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_063 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_063 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middle_four_classification_mask_00817
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_065 (by decide)
  · exact middle_four_classification_mask_00819
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_066 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_067 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_068 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_069 (by decide)
  · exact middle_four_classification_mask_00824
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_070 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_071 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_071 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
