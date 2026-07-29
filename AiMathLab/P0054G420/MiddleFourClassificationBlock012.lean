import AiMathLab.P0054G420.MiddleFourFinite
import AiMathLab.P0054G420.MiddleFourClassificationCheck043
import AiMathLab.P0054G420.MiddleFourClassificationCheck044
import AiMathLab.P0054G420.MiddleFourClassificationCheck045
import AiMathLab.P0054G420.MiddleFourClassificationCheck046
import AiMathLab.P0054G420.MiddleFourClassificationCheck047
import AiMathLab.P0054G420.MiddleFourClassificationCheck048
import AiMathLab.P0054G420.MiddleFourClassificationCheck049
import AiMathLab.P0054G420.MiddleFourClassificationCheck050
import AiMathLab.P0054G420.MiddleFourClassificationCheck051
import AiMathLab.P0054G420.MiddleFourClassificationCheck052
import AiMathLab.P0054G420.MiddleFourClassificationCheck053
import AiMathLab.P0054G420.MiddleFourClassificationCheck054
import AiMathLab.P0054G420.MiddleFourClassificationMask00779
import AiMathLab.P0054G420.MiddleFourClassificationMask00817
import AiMathLab.P0054G420.MiddleFourClassificationMask00819
import AiMathLab.P0054G420.MiddleFourClassificationMask00824

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- A fixed-size block keeps exhaustive mask dispatch incremental.
theorem middle_four_classification_block_012 (offset : Fin 64) :
    middleFourClassificationMaskCheck (768 + offset.val) = true := by
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
  · exact middle_four_classification_mask_00779
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_043 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_044 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_045 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_046 (by decide)
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
      middle_four_classification_group_047 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_047 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_048 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_048 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_048 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_048 (by decide)
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
      middle_four_classification_group_048 (by decide)
  · rfl
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_049 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_049 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_049 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_049 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_050 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_050 (by decide)
  · exact middle_four_classification_mask_00817
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_051 (by decide)
  · exact middle_four_classification_mask_00819
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_052 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_052 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_053 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_053 (by decide)
  · exact middle_four_classification_mask_00824
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · exact middleFourClassificationMaskCheck_of_list
      middle_four_classification_group_054 (by decide)
  · rfl
  · rfl
  · rfl

end AiMathLab.P0054.G420
