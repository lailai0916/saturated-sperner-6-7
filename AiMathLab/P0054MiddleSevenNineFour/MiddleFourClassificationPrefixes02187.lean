import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01677
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0218711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0218712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0218713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0218714
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0218721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0218722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0218731
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0218741

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02187 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [3, 1], [4, 1]].all (middleFourClassificationValuesCheck 2187) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02187_1_1
  · exact middle_four_classification_prefix_02187_1_2
  · exact middle_four_classification_prefix_02187_1_3
  · exact middle_four_classification_prefix_02187_1_4
  · exact middle_four_classification_prefix_02187_2_1
  · exact middle_four_classification_prefix_02187_2_2
  · exact middle_four_classification_prefix_02187_3_1
  · exact middle_four_classification_prefix_02187_4_1

end AiMathLab.P0054.MiddleSevenNineFinite
