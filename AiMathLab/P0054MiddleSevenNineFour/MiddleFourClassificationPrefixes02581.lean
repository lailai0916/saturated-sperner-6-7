import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258123
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258132
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258133
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258141
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258142
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258143
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258151
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258152
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258153
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258161
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258162
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258171

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02581 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 2581) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02581_1_1
  · exact middle_four_classification_prefix_02581_1_2
  · exact middle_four_classification_prefix_02581_1_3
  · exact middle_four_classification_prefix_02581_2_1
  · exact middle_four_classification_prefix_02581_2_2
  · exact middle_four_classification_prefix_02581_2_3
  · exact middle_four_classification_prefix_02581_3_1
  · exact middle_four_classification_prefix_02581_3_2
  · exact middle_four_classification_prefix_02581_3_3
  · exact middle_four_classification_prefix_02581_4_1
  · exact middle_four_classification_prefix_02581_4_2
  · exact middle_four_classification_prefix_02581_4_3
  · exact middle_four_classification_prefix_02581_5_1
  · exact middle_four_classification_prefix_02581_5_2
  · exact middle_four_classification_prefix_02581_5_3
  · exact middle_four_classification_prefix_02581_6_1
  · exact middle_four_classification_prefix_02581_6_2
  · exact middle_four_classification_prefix_02581_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
