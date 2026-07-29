import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08339
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0834711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0834712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0834713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0834721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0834722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0834731

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08347 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 8347) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08347_1_1
  · exact middle_four_classification_prefix_08347_1_2
  · exact middle_four_classification_prefix_08347_1_3
  · exact middle_four_classification_prefix_08347_2_1
  · exact middle_four_classification_prefix_08347_2_2
  · exact middle_four_classification_prefix_08347_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
