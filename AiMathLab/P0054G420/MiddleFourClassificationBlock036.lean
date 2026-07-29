import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck124
import AiMathLab.P0054G420.MiddleFourClassificationCheck125
import AiMathLab.P0054G420.MiddleFourClassificationCheck126
import AiMathLab.P0054G420.MiddleFourClassificationCheck127
import AiMathLab.P0054G420.MiddleFourClassificationCheck128
import AiMathLab.P0054G420.MiddleFourClassificationCheck129
import AiMathLab.P0054G420.MiddleFourClassificationCheck130
import AiMathLab.P0054G420.MiddleFourClassificationCheck131
import AiMathLab.P0054G420.MiddleFourClassificationCheck132
import AiMathLab.P0054G420.MiddleFourClassificationCheck133
import AiMathLab.P0054G420.MiddleFourClassificationCheck134
import AiMathLab.P0054G420.MiddleFourClassificationCheck135
import AiMathLab.P0054G420.MiddleFourClassificationMask02315
import AiMathLab.P0054G420.MiddleFourClassificationMask02341
import AiMathLab.P0054G420.MiddleFourClassificationMask02342
import AiMathLab.P0054G420.MiddleFourClassificationMask02349

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_036 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2304 + offset.val) = true := by
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
  · exact middle_four_classification_mask_02315
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_124 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_125 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_125 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_126 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_126 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_126 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_127 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_128 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_128 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_128 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_129 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_129 (by decide)
  · exact middle_four_classification_mask_02341
  · exact middle_four_classification_mask_02342
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_130 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_130 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_131 (by decide)
  · exact middle_four_classification_mask_02349
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_132 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_132 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_132 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_132 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_133 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_133 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_133 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_134 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_134 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_134 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_135 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.G420
