import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck310
import AiMathLab.P0054G420.MiddleFourClassificationCheck311
import AiMathLab.P0054G420.MiddleFourClassificationCheck312
import AiMathLab.P0054G420.MiddleFourClassificationCheck313

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_104 (offset : Fin 64) :
    middleFourClassificationMaskCheck (6656 + offset.val) = true := by
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
      middle_four_classification_group_310 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_310 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_310 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_311 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_311 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_311 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_311 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_311 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_311 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_312 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_313 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_313 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_313 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
