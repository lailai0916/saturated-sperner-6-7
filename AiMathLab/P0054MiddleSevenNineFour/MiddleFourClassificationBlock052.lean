import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock051
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck325
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck326
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck327

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_052 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3328 + offset.val) = true := by
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
      middle_four_classification_group_322 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_322 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_323 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_323 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_323 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_324 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_324 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_324 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_324 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_325 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_325 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_325 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_326 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_326 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_326 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_327 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_327 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_327 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_327 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_327 (by decide)
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
