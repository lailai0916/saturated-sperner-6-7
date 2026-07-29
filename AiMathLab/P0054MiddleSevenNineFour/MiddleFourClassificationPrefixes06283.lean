import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04491
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0628311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0628312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0628313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0628321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0628331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0628341

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_06283 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [3, 1], [4, 1]].all (middleFourClassificationValuesCheck 6283) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_06283_1_1
  · exact middle_four_classification_prefix_06283_1_2
  · exact middle_four_classification_prefix_06283_1_3
  · exact middle_four_classification_prefix_06283_2_1
  · exact middle_four_classification_prefix_06283_3_1
  · exact middle_four_classification_prefix_06283_4_1

end AiMathLab.P0054.MiddleSevenNineFinite
