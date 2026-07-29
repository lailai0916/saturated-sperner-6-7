import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02187
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224317
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224371

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02243 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 2243) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02243_1_1
  · exact middle_four_classification_prefix_02243_1_2
  · exact middle_four_classification_prefix_02243_1_3
  · exact middle_four_classification_prefix_02243_1_4
  · exact middle_four_classification_prefix_02243_1_5
  · exact middle_four_classification_prefix_02243_1_6
  · exact middle_four_classification_prefix_02243_1_7
  · exact middle_four_classification_prefix_02243_2_1
  · exact middle_four_classification_prefix_02243_2_2
  · exact middle_four_classification_prefix_02243_2_3
  · exact middle_four_classification_prefix_02243_3_1
  · exact middle_four_classification_prefix_02243_3_2
  · exact middle_four_classification_prefix_02243_4_1
  · exact middle_four_classification_prefix_02243_5_1
  · exact middle_four_classification_prefix_02243_6_1
  · exact middle_four_classification_prefix_02243_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
