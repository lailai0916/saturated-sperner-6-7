import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01193
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123141
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0123151

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01231 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 1231) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01231_1_1
  · exact middle_four_classification_prefix_01231_1_2
  · exact middle_four_classification_prefix_01231_1_3
  · exact middle_four_classification_prefix_01231_1_4
  · exact middle_four_classification_prefix_01231_1_5
  · exact middle_four_classification_prefix_01231_2_1
  · exact middle_four_classification_prefix_01231_2_2
  · exact middle_four_classification_prefix_01231_3_1
  · exact middle_four_classification_prefix_01231_4_1
  · exact middle_four_classification_prefix_01231_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
