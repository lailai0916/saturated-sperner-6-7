import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02349
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0246811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0246812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0246813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0246821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0246822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0246831

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02468 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 2468) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02468_1_1
  · exact middle_four_classification_prefix_02468_1_2
  · exact middle_four_classification_prefix_02468_1_3
  · exact middle_four_classification_prefix_02468_2_1
  · exact middle_four_classification_prefix_02468_2_2
  · exact middle_four_classification_prefix_02468_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
