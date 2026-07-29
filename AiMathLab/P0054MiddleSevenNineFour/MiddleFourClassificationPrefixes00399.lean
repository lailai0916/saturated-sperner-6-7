import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00398
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039961

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00399 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 399) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00399_1_1
  · exact middle_four_classification_prefix_00399_1_2
  · exact middle_four_classification_prefix_00399_1_3
  · exact middle_four_classification_prefix_00399_2_1
  · exact middle_four_classification_prefix_00399_2_2
  · exact middle_four_classification_prefix_00399_3_1
  · exact middle_four_classification_prefix_00399_4_1
  · exact middle_four_classification_prefix_00399_5_1
  · exact middle_four_classification_prefix_00399_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
