import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck071
import AiMathLab.P0054G420.MiddleFourClassificationCheck072
import AiMathLab.P0054G420.MiddleFourClassificationCheck073
import AiMathLab.P0054G420.MiddleFourClassificationCheck074

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_015 (offset : Fin 64) :
    middleFourClassificationMaskCheck (960 + offset.val) = true := by
  fin_cases offset
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_071 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_071 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_072 (by decide)
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
      middle_four_classification_group_073 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_073 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_073 (by decide)
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
      middle_four_classification_group_073 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_073 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_074 (by decide)
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
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
