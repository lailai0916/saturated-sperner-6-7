import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04635
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0842711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0842712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0842713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0842714
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0842715
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0842721

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08427 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 1]].all (middleFourClassificationValuesCheck 8427) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08427_1_1
  · exact middle_four_classification_prefix_08427_1_2
  · exact middle_four_classification_prefix_08427_1_3
  · exact middle_four_classification_prefix_08427_1_4
  · exact middle_four_classification_prefix_08427_1_5
  · exact middle_four_classification_prefix_08427_2_1

end AiMathLab.P0054.MiddleSevenNineFinite
