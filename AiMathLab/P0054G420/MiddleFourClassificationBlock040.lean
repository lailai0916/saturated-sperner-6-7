import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck154
import AiMathLab.P0054G420.MiddleFourClassificationCheck155
import AiMathLab.P0054G420.MiddleFourClassificationCheck156
import AiMathLab.P0054G420.MiddleFourClassificationCheck157
import AiMathLab.P0054G420.MiddleFourClassificationCheck158
import AiMathLab.P0054G420.MiddleFourClassificationCheck159
import AiMathLab.P0054G420.MiddleFourClassificationCheck160
import AiMathLab.P0054G420.MiddleFourClassificationCheck161
import AiMathLab.P0054G420.MiddleFourClassificationCheck162
import AiMathLab.P0054G420.MiddleFourClassificationCheck163
import AiMathLab.P0054G420.MiddleFourClassificationCheck164
import AiMathLab.P0054G420.MiddleFourClassificationCheck165
import AiMathLab.P0054G420.MiddleFourClassificationMask02571
import AiMathLab.P0054G420.MiddleFourClassificationMask02581
import AiMathLab.P0054G420.MiddleFourClassificationMask02582
import AiMathLab.P0054G420.MiddleFourClassificationMask02590

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_040 (offset : Fin 64) :
    middleFourClassificationMaskCheck (2560 + offset.val) = true := by
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
  · exact middle_four_classification_mask_02571
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_154 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_155 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_155 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_156 (by decide)
  · exact middle_four_classification_mask_02581
  · exact middle_four_classification_mask_02582
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_156 (by decide)
  · rfl
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_157 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_158 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_159 (by decide)
  · exact middle_four_classification_mask_02590
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_159 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_159 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_160 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_160 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_160 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_161 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_162 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_162 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_162 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_162 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_163 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_163 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_163 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_164 (by decide)
  · rfl
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_164 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_164 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_165 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_165 (by decide)
  · rfl

end AiMathLab.P0054.G420
