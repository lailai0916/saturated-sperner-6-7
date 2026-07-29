import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck214
import AiMathLab.P0054G420.MiddleFourClassificationCheck215
import AiMathLab.P0054G420.MiddleFourClassificationCheck216
import AiMathLab.P0054G420.MiddleFourClassificationCheck217
import AiMathLab.P0054G420.MiddleFourClassificationCheck218
import AiMathLab.P0054G420.MiddleFourClassificationCheck219
import AiMathLab.P0054G420.MiddleFourClassificationCheck220
import AiMathLab.P0054G420.MiddleFourClassificationCheck221

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_050 (offset : Fin 64) :
    middleFourClassificationMaskCheck (3200 + offset.val) = true := by
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
      middle_four_classification_group_214 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_215 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_215 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_216 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_216 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_216 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_217 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_217 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_217 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_218 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_219 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_219 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_219 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_220 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_221 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_221 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_221 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_221 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
