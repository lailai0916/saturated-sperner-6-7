import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01422
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0142311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0142312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0142313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0142321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0142322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0142331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0142341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0142351

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01423 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 1423) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01423_1_1
  · exact middle_four_classification_prefix_01423_1_2
  · exact middle_four_classification_prefix_01423_1_3
  · exact middle_four_classification_prefix_01423_2_1
  · exact middle_four_classification_prefix_01423_2_2
  · exact middle_four_classification_prefix_01423_3_1
  · exact middle_four_classification_prefix_01423_4_1
  · exact middle_four_classification_prefix_01423_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
