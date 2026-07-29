import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00243
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116317
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116318
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116371
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0116381

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01163 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [2, 1], [2, 2], [2, 3], [2, 4], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [6, 1], [7, 1], [8, 1]].all (middleFourClassificationValuesCheck 1163) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01163_1_1
  · exact middle_four_classification_prefix_01163_1_2
  · exact middle_four_classification_prefix_01163_1_3
  · exact middle_four_classification_prefix_01163_1_4
  · exact middle_four_classification_prefix_01163_1_5
  · exact middle_four_classification_prefix_01163_1_6
  · exact middle_four_classification_prefix_01163_1_7
  · exact middle_four_classification_prefix_01163_1_8
  · exact middle_four_classification_prefix_01163_2_1
  · exact middle_four_classification_prefix_01163_2_2
  · exact middle_four_classification_prefix_01163_2_3
  · exact middle_four_classification_prefix_01163_2_4
  · exact middle_four_classification_prefix_01163_3_1
  · exact middle_four_classification_prefix_01163_3_2
  · exact middle_four_classification_prefix_01163_4_1
  · exact middle_four_classification_prefix_01163_4_2
  · exact middle_four_classification_prefix_01163_5_1
  · exact middle_four_classification_prefix_01163_6_1
  · exact middle_four_classification_prefix_01163_7_1
  · exact middle_four_classification_prefix_01163_8_1

end AiMathLab.P0054.MiddleSevenNineFinite
