import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023711
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023712
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023713
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023721
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023722
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023731
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023732
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023741
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0023751

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00237 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 237) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00237_1_1
  · exact middle_four_classification_prefix_00237_1_2
  · exact middle_four_classification_prefix_00237_1_3
  · exact middle_four_classification_prefix_00237_2_1
  · exact middle_four_classification_prefix_00237_2_2
  · exact middle_four_classification_prefix_00237_3_1
  · exact middle_four_classification_prefix_00237_3_2
  · exact middle_four_classification_prefix_00237_4_1
  · exact middle_four_classification_prefix_00237_5_1

end AiMathLab.P0054.G420
