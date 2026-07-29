import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04515
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833331

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08333 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 8333) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08333_1_1
  · exact middle_four_classification_prefix_08333_1_2
  · exact middle_four_classification_prefix_08333_1_3
  · exact middle_four_classification_prefix_08333_2_1
  · exact middle_four_classification_prefix_08333_2_2
  · exact middle_four_classification_prefix_08333_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
