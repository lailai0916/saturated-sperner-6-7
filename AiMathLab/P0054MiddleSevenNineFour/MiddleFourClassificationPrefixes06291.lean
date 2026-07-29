import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04619
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629141
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629151
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629161

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_06291 :
    [[1, 1], [1, 2], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 6291) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_06291_1_1
  · exact middle_four_classification_prefix_06291_1_2
  · exact middle_four_classification_prefix_06291_2_1
  · exact middle_four_classification_prefix_06291_3_1
  · exact middle_four_classification_prefix_06291_4_1
  · exact middle_four_classification_prefix_06291_5_1
  · exact middle_four_classification_prefix_06291_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
