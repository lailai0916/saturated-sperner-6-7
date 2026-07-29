import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02211
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234123
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234132
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234133
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234141
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234142
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234143
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234151
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234152
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234153
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234161
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234162
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234171

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02341 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 2341) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02341_1_1
  · exact middle_four_classification_prefix_02341_1_2
  · exact middle_four_classification_prefix_02341_1_3
  · exact middle_four_classification_prefix_02341_2_1
  · exact middle_four_classification_prefix_02341_2_2
  · exact middle_four_classification_prefix_02341_2_3
  · exact middle_four_classification_prefix_02341_3_1
  · exact middle_four_classification_prefix_02341_3_2
  · exact middle_four_classification_prefix_02341_3_3
  · exact middle_four_classification_prefix_02341_4_1
  · exact middle_four_classification_prefix_02341_4_2
  · exact middle_four_classification_prefix_02341_4_3
  · exact middle_four_classification_prefix_02341_5_1
  · exact middle_four_classification_prefix_02341_5_2
  · exact middle_four_classification_prefix_02341_5_3
  · exact middle_four_classification_prefix_02341_6_1
  · exact middle_four_classification_prefix_02341_6_2
  · exact middle_four_classification_prefix_02341_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
