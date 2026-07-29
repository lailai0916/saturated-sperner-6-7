import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock045
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck281
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck282
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck283
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck284
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck285
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck286
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck287
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck288
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck289

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_046 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2944 + offset.val) = true := by
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
      middle_four_classification_group_281 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_281 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_282 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_283 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_284 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_284 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_284 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_285 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_285 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_285 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_286 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_286 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_287 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_287 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_287 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_288 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_288 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_288 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_289 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
