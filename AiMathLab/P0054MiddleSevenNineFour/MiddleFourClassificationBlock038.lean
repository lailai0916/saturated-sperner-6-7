import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock037
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck206
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck207
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck208
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck209
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck210
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck211
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck212
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck213
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck214
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck215
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationMask02470

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_038 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2432 + offset.val) = true := by
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
      middle_four_classification_group_206 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_207 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_207 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_208 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_209 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_209 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_210 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_211 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_211 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_212 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_213 (by decide)
  · exact middle_four_classification_mask_02470
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_213 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_214 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_214 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_214 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_215 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_215 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_215 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_215 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_215 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_215 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
