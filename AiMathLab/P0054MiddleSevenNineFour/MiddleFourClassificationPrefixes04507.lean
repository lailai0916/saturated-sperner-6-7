import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04506
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450731
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450741
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450751

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04507 :
    [[1, 1], [2, 1], [3, 1], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 4507) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04507_1_1
  · exact middle_four_classification_prefix_04507_2_1
  · exact middle_four_classification_prefix_04507_3_1
  · exact middle_four_classification_prefix_04507_4_1
  · exact middle_four_classification_prefix_04507_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
