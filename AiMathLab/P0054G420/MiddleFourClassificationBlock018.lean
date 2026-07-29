import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck075
import AiMathLab.P0054G420.MiddleFourClassificationCheck076
import AiMathLab.P0054G420.MiddleFourClassificationCheck077
import AiMathLab.P0054G420.MiddleFourClassificationCheck078
import AiMathLab.P0054G420.MiddleFourClassificationCheck079
import AiMathLab.P0054G420.MiddleFourClassificationCheck080
import AiMathLab.P0054G420.MiddleFourClassificationCheck081
import AiMathLab.P0054G420.MiddleFourClassificationCheck082
import AiMathLab.P0054G420.MiddleFourClassificationCheck083
import AiMathLab.P0054G420.MiddleFourClassificationCheck084
import AiMathLab.P0054G420.MiddleFourClassificationMask01163
import AiMathLab.P0054G420.MiddleFourClassificationMask01167
import AiMathLab.P0054G420.MiddleFourClassificationMask01178
import AiMathLab.P0054G420.MiddleFourClassificationMask01193

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_018 (offset : Fin 64) :
    middleFourClassificationMaskCheck (1152 + offset.val) = true := by
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
  · exact middle_four_classification_mask_01163
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_01167
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
  · exact middle_four_classification_mask_01178
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_075 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_076 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_076 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middle_four_classification_mask_01193
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_077 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_078 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_078 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_079 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_079 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_080 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_081 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_081 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_082 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_082 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_082 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_083 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_083 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_084 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_084 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_084 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_084 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_084 (by decide)
  · rfl

end AiMathLab.P0054.G420
