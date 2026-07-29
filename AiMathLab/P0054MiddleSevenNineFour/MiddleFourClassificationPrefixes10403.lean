import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08873
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1040311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1040312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1040313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1040314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1040315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1040316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1040321

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_10403 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1]].all (middleFourClassificationValuesCheck 10403) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_10403_1_1
  · exact middle_four_classification_prefix_10403_1_2
  · exact middle_four_classification_prefix_10403_1_3
  · exact middle_four_classification_prefix_10403_1_4
  · exact middle_four_classification_prefix_10403_1_5
  · exact middle_four_classification_prefix_10403_1_6
  · exact middle_four_classification_prefix_10403_2_1

end AiMathLab.P0054.MiddleSevenNineFinite
