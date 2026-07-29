import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck135
import AiMathLab.P0054G420.MiddleFourClassificationCheck136
import AiMathLab.P0054G420.MiddleFourClassificationCheck137
import AiMathLab.P0054G420.MiddleFourClassificationCheck138
import AiMathLab.P0054G420.MiddleFourClassificationCheck139
import AiMathLab.P0054G420.MiddleFourClassificationCheck140
import AiMathLab.P0054G420.MiddleFourClassificationCheck141
import AiMathLab.P0054G420.MiddleFourClassificationCheck142
import AiMathLab.P0054G420.MiddleFourClassificationCheck143
import AiMathLab.P0054G420.MiddleFourClassificationCheck144
import AiMathLab.P0054G420.MiddleFourClassificationCheck145

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_037 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2368 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_135 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_136 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_137 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_137 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_138 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_139 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_139 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_140 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_140 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_140 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_140 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_140 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_141 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_141 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_141 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_142 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_142 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_142 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_142 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_142 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_143 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_143 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_143 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_144 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_145 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_145 (by decide)
  · rfl
  · rfl

end AiMathLab.P0054.G420
