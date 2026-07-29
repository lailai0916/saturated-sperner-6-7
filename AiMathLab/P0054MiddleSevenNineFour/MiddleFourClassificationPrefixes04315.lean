import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes03087
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0431511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0431512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0431521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0431531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0431541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0431551

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04315 :
    [[1, 1], [1, 2], [2, 1], [3, 1], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 4315) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04315_1_1
  · exact middle_four_classification_prefix_04315_1_2
  · exact middle_four_classification_prefix_04315_2_1
  · exact middle_four_classification_prefix_04315_3_1
  · exact middle_four_classification_prefix_04315_4_1
  · exact middle_four_classification_prefix_04315_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
