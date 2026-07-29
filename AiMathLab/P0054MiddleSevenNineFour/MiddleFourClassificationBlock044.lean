import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationBlock043
import AiMathLab.P0054MiddleSevenNineFourFinite
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck268
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck269
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck270
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck271
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck272
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck273
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck274
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck275
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationCheck276

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_044 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2816 + offset.val) = true := by
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
      middle_four_classification_group_268 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_268 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_269 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_269 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_269 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_269 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_270 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_271 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_271 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_272 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_272 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_272 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_272 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_272 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_272 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_273 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_273 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_274 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_274 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_274 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_275 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_275 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_275 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_275 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_275 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_276 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_276 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_276 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_276 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.MiddleSevenNineFinite
