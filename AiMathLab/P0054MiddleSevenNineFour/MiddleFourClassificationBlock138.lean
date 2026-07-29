import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock137
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck517
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck518
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck519
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck520
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck523
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck524
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck525
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08843
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask08873

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_138 (offset : Fin 64) :
    middleFourClassificationMaskCheck (8832 + offset.val) = true := by
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
  · exact middle_four_classification_mask_08843
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_517 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_518 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_519 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_520 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_520 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_521 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_521 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_522 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_522 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_522 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_522 (by decide)
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
  · exact middle_four_classification_mask_08873
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_523 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_524 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_524 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_524 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_524 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_524 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_524 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_525 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_525 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
