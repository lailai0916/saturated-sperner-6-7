import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833515
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833516
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833531

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08335 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 8335) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08335_1_1
  · exact middle_four_classification_prefix_08335_1_2
  · exact middle_four_classification_prefix_08335_1_3
  · exact middle_four_classification_prefix_08335_1_4
  · exact middle_four_classification_prefix_08335_1_5
  · exact middle_four_classification_prefix_08335_1_6
  · exact middle_four_classification_prefix_08335_2_1
  · exact middle_four_classification_prefix_08335_2_2
  · exact middle_four_classification_prefix_08335_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
