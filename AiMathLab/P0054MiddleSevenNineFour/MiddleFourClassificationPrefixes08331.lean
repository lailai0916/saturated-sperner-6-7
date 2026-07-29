import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes06283
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833116
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833117
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833118
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833123
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833132
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833141

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08331 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1]].all (middleFourClassificationValuesCheck 8331) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08331_1_1
  · exact middle_four_classification_prefix_08331_1_2
  · exact middle_four_classification_prefix_08331_1_3
  · exact middle_four_classification_prefix_08331_1_4
  · exact middle_four_classification_prefix_08331_1_5
  · exact middle_four_classification_prefix_08331_1_6
  · exact middle_four_classification_prefix_08331_1_7
  · exact middle_four_classification_prefix_08331_1_8
  · exact middle_four_classification_prefix_08331_2_1
  · exact middle_four_classification_prefix_08331_2_2
  · exact middle_four_classification_prefix_08331_2_3
  · exact middle_four_classification_prefix_08331_3_1
  · exact middle_four_classification_prefix_08331_3_2
  · exact middle_four_classification_prefix_08331_4_1

end AiMathLab.P0054.MiddleSevenNineFinite
