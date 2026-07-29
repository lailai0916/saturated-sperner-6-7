import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock075
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck406
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck407
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck408
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck409
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck410
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck411

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_076 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4864 + offset.val) = true := by
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
      middle_four_classification_group_406 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_406 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_407 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_407 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_407 (by decide)
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
      middle_four_classification_group_407 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_408 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_408 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_408 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_409 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_409 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_409 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_410 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_410 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_410 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_410 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_410 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_410 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_411 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_411 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
