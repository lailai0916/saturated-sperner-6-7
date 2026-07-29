import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01675
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180325
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180334
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180343
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180352
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0180361

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01803 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [3, 1], [3, 2], [3, 3], [3, 4], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [6, 1]].all (middleFourClassificationValuesCheck 1803) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01803_1_1
  · exact middle_four_classification_prefix_01803_1_2
  · exact middle_four_classification_prefix_01803_1_3
  · exact middle_four_classification_prefix_01803_1_4
  · exact middle_four_classification_prefix_01803_1_5
  · exact middle_four_classification_prefix_01803_1_6
  · exact middle_four_classification_prefix_01803_2_1
  · exact middle_four_classification_prefix_01803_2_2
  · exact middle_four_classification_prefix_01803_2_3
  · exact middle_four_classification_prefix_01803_2_4
  · exact middle_four_classification_prefix_01803_2_5
  · exact middle_four_classification_prefix_01803_3_1
  · exact middle_four_classification_prefix_01803_3_2
  · exact middle_four_classification_prefix_01803_3_3
  · exact middle_four_classification_prefix_01803_3_4
  · exact middle_four_classification_prefix_01803_4_1
  · exact middle_four_classification_prefix_01803_4_2
  · exact middle_four_classification_prefix_01803_4_3
  · exact middle_four_classification_prefix_01803_5_1
  · exact middle_four_classification_prefix_01803_5_2
  · exact middle_four_classification_prefix_01803_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
