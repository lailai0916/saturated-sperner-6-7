import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock167
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck568
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck569
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck570
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck571
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck572
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck573
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck574
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck575
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck576
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask10763

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_168 (offset : Fin 64) :
    middleFourClassificationMaskCheck (10752 + offset.val) = true := by
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
  · exact middle_four_classification_mask_10763
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_568 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_568 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_568 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_568 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_569 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_569 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_569 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_570 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_571 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_572 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_572 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_572 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_573 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_574 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_574 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_574 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_575 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_575 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_575 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_575 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_575 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_576 (by decide)
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
