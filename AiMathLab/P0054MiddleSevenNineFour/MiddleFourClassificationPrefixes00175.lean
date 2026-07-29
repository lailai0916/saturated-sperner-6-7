import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00173
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017515
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017516
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017531

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00175 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 175) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00175_1_1
  · exact middle_four_classification_prefix_00175_1_2
  · exact middle_four_classification_prefix_00175_1_3
  · exact middle_four_classification_prefix_00175_1_4
  · exact middle_four_classification_prefix_00175_1_5
  · exact middle_four_classification_prefix_00175_1_6
  · exact middle_four_classification_prefix_00175_2_1
  · exact middle_four_classification_prefix_00175_2_2
  · exact middle_four_classification_prefix_00175_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
