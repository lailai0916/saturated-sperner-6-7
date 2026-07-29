import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08459
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887321

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08873 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1]].all (middleFourClassificationValuesCheck 8873) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08873_1_1
  · exact middle_four_classification_prefix_08873_1_2
  · exact middle_four_classification_prefix_08873_1_3
  · exact middle_four_classification_prefix_08873_1_4
  · exact middle_four_classification_prefix_08873_1_5
  · exact middle_four_classification_prefix_08873_1_6
  · exact middle_four_classification_prefix_08873_2_1

end AiMathLab.P0054.MiddleSevenNineFinite
