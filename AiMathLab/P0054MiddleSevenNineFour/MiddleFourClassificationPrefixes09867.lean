import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08875
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0986711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0986712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0986713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0986714
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0986715
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0986721

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_09867 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 1]].all (middleFourClassificationValuesCheck 9867) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_09867_1_1
  · exact middle_four_classification_prefix_09867_1_2
  · exact middle_four_classification_prefix_09867_1_3
  · exact middle_four_classification_prefix_09867_1_4
  · exact middle_four_classification_prefix_09867_1_5
  · exact middle_four_classification_prefix_09867_2_1

end AiMathLab.P0054.MiddleSevenNineFinite
