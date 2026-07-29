import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck111
import AiMathLab.P0054G420.MiddleFourClassificationCheck112
import AiMathLab.P0054G420.MiddleFourClassificationCheck113
import AiMathLab.P0054G420.MiddleFourClassificationCheck114
import AiMathLab.P0054G420.MiddleFourClassificationCheck115
import AiMathLab.P0054G420.MiddleFourClassificationCheck116
import AiMathLab.P0054G420.MiddleFourClassificationCheck117
import AiMathLab.P0054G420.MiddleFourClassificationCheck118
import AiMathLab.P0054G420.MiddleFourClassificationCheck119
import AiMathLab.P0054G420.MiddleFourClassificationMask02187
import AiMathLab.P0054G420.MiddleFourClassificationMask02195

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_034 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2176 + offset.val) = true := by
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
  · exact middle_four_classification_mask_02187
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_111 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_02195
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_112 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_112 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_113 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_114 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_114 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_115 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_116 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_116 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_117 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_118 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_118 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_118 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_118 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_118 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_118 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_118 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_119 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_119 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_119 (by decide)
  · rfl

end AiMathLab.P0054.G420
