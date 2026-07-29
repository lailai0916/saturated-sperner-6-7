import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04238
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451532
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451542
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451551
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451552
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0451561

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04515 :
    [[1, 1], [1, 2], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [5, 2], [6, 1]].all (middleFourClassificationValuesCheck 4515) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04515_1_1
  · exact middle_four_classification_prefix_04515_1_2
  · exact middle_four_classification_prefix_04515_2_1
  · exact middle_four_classification_prefix_04515_2_2
  · exact middle_four_classification_prefix_04515_3_1
  · exact middle_four_classification_prefix_04515_3_2
  · exact middle_four_classification_prefix_04515_4_1
  · exact middle_four_classification_prefix_04515_4_2
  · exact middle_four_classification_prefix_04515_5_1
  · exact middle_four_classification_prefix_04515_5_2
  · exact middle_four_classification_prefix_04515_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
