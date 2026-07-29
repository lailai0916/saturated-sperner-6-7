import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04259
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0426711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0426712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0426713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0426721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0426722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0426731

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04267 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 4267) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04267_1_1
  · exact middle_four_classification_prefix_04267_1_2
  · exact middle_four_classification_prefix_04267_1_3
  · exact middle_four_classification_prefix_04267_2_1
  · exact middle_four_classification_prefix_04267_2_2
  · exact middle_four_classification_prefix_04267_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
