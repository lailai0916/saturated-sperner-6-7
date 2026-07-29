import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08843
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885116
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885123
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885124
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0885125

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08851 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5]].all (middleFourClassificationValuesCheck 8851) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08851_1_1
  · exact middle_four_classification_prefix_08851_1_2
  · exact middle_four_classification_prefix_08851_1_3
  · exact middle_four_classification_prefix_08851_1_4
  · exact middle_four_classification_prefix_08851_1_5
  · exact middle_four_classification_prefix_08851_1_6
  · exact middle_four_classification_prefix_08851_2_1
  · exact middle_four_classification_prefix_08851_2_2
  · exact middle_four_classification_prefix_08851_2_3
  · exact middle_four_classification_prefix_08851_2_4
  · exact middle_four_classification_prefix_08851_2_5

end AiMathLab.P0054.MiddleSevenNineFinite
