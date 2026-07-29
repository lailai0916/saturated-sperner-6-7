import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08873
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0887515

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08875 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5]].all (middleFourClassificationValuesCheck 8875) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08875_1_1
  · exact middle_four_classification_prefix_08875_1_2
  · exact middle_four_classification_prefix_08875_1_3
  · exact middle_four_classification_prefix_08875_1_4
  · exact middle_four_classification_prefix_08875_1_5

end AiMathLab.P0054.MiddleSevenNineFinite
