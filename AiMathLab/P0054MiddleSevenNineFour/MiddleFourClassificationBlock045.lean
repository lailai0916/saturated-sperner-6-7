import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock044
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck277
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck278
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck279
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck280
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck281

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_045 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2880 + offset.val) = true := by
  fin_cases offset
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_277 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_277 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_277 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_278 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_279 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_280 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
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
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
