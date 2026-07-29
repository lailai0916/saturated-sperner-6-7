import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00779
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0078351

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00783 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 1], [2, 2], [2, 3], [2, 4], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1]].all (middleFourClassificationValuesCheck 783) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00783_1_1
  · exact middle_four_classification_prefix_00783_1_2
  · exact middle_four_classification_prefix_00783_1_3
  · exact middle_four_classification_prefix_00783_1_4
  · exact middle_four_classification_prefix_00783_1_5
  · exact middle_four_classification_prefix_00783_2_1
  · exact middle_four_classification_prefix_00783_2_2
  · exact middle_four_classification_prefix_00783_2_3
  · exact middle_four_classification_prefix_00783_2_4
  · exact middle_four_classification_prefix_00783_3_1
  · exact middle_four_classification_prefix_00783_3_2
  · exact middle_four_classification_prefix_00783_3_3
  · exact middle_four_classification_prefix_00783_4_1
  · exact middle_four_classification_prefix_00783_4_2
  · exact middle_four_classification_prefix_00783_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
