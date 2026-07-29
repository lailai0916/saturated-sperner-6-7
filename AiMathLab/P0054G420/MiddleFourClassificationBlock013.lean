import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck055
import AiMathLab.P0054G420.MiddleFourClassificationCheck056
import AiMathLab.P0054G420.MiddleFourClassificationCheck057
import AiMathLab.P0054G420.MiddleFourClassificationCheck058
import AiMathLab.P0054G420.MiddleFourClassificationCheck059
import AiMathLab.P0054G420.MiddleFourClassificationCheck060
import AiMathLab.P0054G420.MiddleFourClassificationCheck061
import AiMathLab.P0054G420.MiddleFourClassificationCheck062
import AiMathLab.P0054G420.MiddleFourClassificationCheck063
import AiMathLab.P0054G420.MiddleFourClassificationCheck064

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_013 (offset : Fin 64) :
    middleFourClassificationMaskCheck (832 + offset.val) = true := by
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
      middle_four_classification_group_055 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_056 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_057 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_058 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_058 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_059 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_059 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_059 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_060 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_060 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_061 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_061 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_061 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_061 (by decide)
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
      middle_four_classification_group_061 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_062 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_062 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_062 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_062 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_062 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_063 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_063 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_063 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_063 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_064 (by decide)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
