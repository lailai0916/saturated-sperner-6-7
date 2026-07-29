import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04635
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0551511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0551512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0551521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0551531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0551541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0551551

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_05515 :
    [[1, 1], [1, 2], [2, 1], [3, 1], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 5515) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_05515_1_1
  · exact middle_four_classification_prefix_05515_1_2
  · exact middle_four_classification_prefix_05515_2_1
  · exact middle_four_classification_prefix_05515_3_1
  · exact middle_four_classification_prefix_05515_4_1
  · exact middle_four_classification_prefix_05515_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
