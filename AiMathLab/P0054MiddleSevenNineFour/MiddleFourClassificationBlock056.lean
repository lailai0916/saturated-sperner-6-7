import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock055
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck334
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck335
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck336
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck337
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck338
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck339

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_056 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3584 + offset.val) = true := by
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
      middle_four_classification_group_334 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_334 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_335 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_335 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_335 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_335 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_336 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_336 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_336 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_337 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_337 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_337 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_338 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_339 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_339 (by decide)
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
