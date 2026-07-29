import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock161
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck549
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck550
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck551
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck552
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck553
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck554
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck555
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck556
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask10379
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask10403

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_162 (offset : Fin 64) :
    middleFourClassificationMaskCheck (10368 + offset.val) = true := by
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
  · exact middle_four_classification_mask_10379
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_549 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_550 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_550 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_551 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_551 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_551 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_551 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_552 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_553 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_553 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_554 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_10403
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_554 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_554 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_555 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_556 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_556 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_556 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_556 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_556 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_556 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
