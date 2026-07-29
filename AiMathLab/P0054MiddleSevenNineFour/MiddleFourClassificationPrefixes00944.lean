import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00843
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0094411
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0094412
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0094413
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0094421
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0094422
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0094431

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00944 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 944) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00944_1_1
  · exact middle_four_classification_prefix_00944_1_2
  · exact middle_four_classification_prefix_00944_1_3
  · exact middle_four_classification_prefix_00944_2_1
  · exact middle_four_classification_prefix_00944_2_2
  · exact middle_four_classification_prefix_00944_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
