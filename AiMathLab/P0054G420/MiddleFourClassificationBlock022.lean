import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck089
import AiMathLab.P0054G420.MiddleFourClassificationCheck090
import AiMathLab.P0054G420.MiddleFourClassificationCheck091
import AiMathLab.P0054G420.MiddleFourClassificationCheck092
import AiMathLab.P0054G420.MiddleFourClassificationCheck093
import AiMathLab.P0054G420.MiddleFourClassificationCheck094
import AiMathLab.P0054G420.MiddleFourClassificationMask01419
import AiMathLab.P0054G420.MiddleFourClassificationMask01422

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_022 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1408 + offset.val) = true := by
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
  · exact middle_four_classification_mask_01419
  · rfl
  · rfl
  · exact middle_four_classification_mask_01422
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_089 (by decide)
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
      middle_four_classification_group_090 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_090 (by decide)
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
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_091 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_092 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_092 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_092 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_092 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_093 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_093 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_093 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_094 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_094 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_094 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_094 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_094 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_094 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
