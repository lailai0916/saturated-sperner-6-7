import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock049
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck317
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck318
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck319
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck320
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck321

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_050 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3200 + offset.val) = true := by
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
      middle_four_classification_group_311 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_313 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_314 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_314 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_315 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_315 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_315 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_316 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_317 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_318 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_318 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_319 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_319 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_319 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_320 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_320 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_320 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_320 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_320 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_320 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_321 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
