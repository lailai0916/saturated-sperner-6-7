import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01677
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167915
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167931

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01679 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 1679) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01679_1_1
  · exact middle_four_classification_prefix_01679_1_2
  · exact middle_four_classification_prefix_01679_1_3
  · exact middle_four_classification_prefix_01679_1_4
  · exact middle_four_classification_prefix_01679_1_5
  · exact middle_four_classification_prefix_01679_2_1
  · exact middle_four_classification_prefix_01679_2_2
  · exact middle_four_classification_prefix_01679_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
