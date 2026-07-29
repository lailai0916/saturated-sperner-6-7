import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00458
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065116
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065117
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065118
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065123
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065132
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065141

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00651 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1]].all (middleFourClassificationValuesCheck 651) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00651_1_1
  · exact middle_four_classification_prefix_00651_1_2
  · exact middle_four_classification_prefix_00651_1_3
  · exact middle_four_classification_prefix_00651_1_4
  · exact middle_four_classification_prefix_00651_1_5
  · exact middle_four_classification_prefix_00651_1_6
  · exact middle_four_classification_prefix_00651_1_7
  · exact middle_four_classification_prefix_00651_1_8
  · exact middle_four_classification_prefix_00651_2_1
  · exact middle_four_classification_prefix_00651_2_2
  · exact middle_four_classification_prefix_00651_2_3
  · exact middle_four_classification_prefix_00651_3_1
  · exact middle_four_classification_prefix_00651_3_2
  · exact middle_four_classification_prefix_00651_4_1

end AiMathLab.P0054.MiddleSevenNineFinite
