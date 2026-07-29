import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock071
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck376
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck377
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck378
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck379
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck380
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck381
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck382
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck383
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck384
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck385
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck386
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck387
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck388
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck389
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck390
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04619
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask04635

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_072 (offset : Fin 64) :
    middleFourClassificationMaskCheck (4608 + offset.val) = true := by
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
  · exact middle_four_classification_mask_04619
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_376 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_377 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_378 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_379 (by decide)
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
  · exact middle_four_classification_mask_04635
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_380 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_381 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_381 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_382 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_382 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_383 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_383 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_384 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_384 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_384 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_385 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_386 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_387 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_387 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_387 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_387 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_388 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_388 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_388 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_389 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_389 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_390 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_390 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_390 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
