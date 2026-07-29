import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01803
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0193111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0193112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0193113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0193121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0193131

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01931 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [3, 1]].all (middleFourClassificationValuesCheck 1931) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01931_1_1
  · exact middle_four_classification_prefix_01931_1_2
  · exact middle_four_classification_prefix_01931_1_3
  · exact middle_four_classification_prefix_01931_2_1
  · exact middle_four_classification_prefix_01931_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
