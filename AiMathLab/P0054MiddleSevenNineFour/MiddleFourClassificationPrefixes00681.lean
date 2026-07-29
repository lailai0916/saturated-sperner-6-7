import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00490
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068116
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068117
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0068131

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00681 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 681) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00681_1_1
  · exact middle_four_classification_prefix_00681_1_2
  · exact middle_four_classification_prefix_00681_1_3
  · exact middle_four_classification_prefix_00681_1_4
  · exact middle_four_classification_prefix_00681_1_5
  · exact middle_four_classification_prefix_00681_1_6
  · exact middle_four_classification_prefix_00681_1_7
  · exact middle_four_classification_prefix_00681_2_1
  · exact middle_four_classification_prefix_00681_2_2
  · exact middle_four_classification_prefix_00681_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
