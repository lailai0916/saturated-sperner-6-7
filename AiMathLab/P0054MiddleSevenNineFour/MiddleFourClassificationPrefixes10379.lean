import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08843
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1037911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1037912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1037913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1037914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1037921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1037931

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_10379 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [3, 1]].all (middleFourClassificationValuesCheck 10379) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_10379_1_1
  · exact middle_four_classification_prefix_10379_1_2
  · exact middle_four_classification_prefix_10379_1_3
  · exact middle_four_classification_prefix_10379_1_4
  · exact middle_four_classification_prefix_10379_2_1
  · exact middle_four_classification_prefix_10379_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
