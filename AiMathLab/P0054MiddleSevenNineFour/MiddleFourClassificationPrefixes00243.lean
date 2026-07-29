import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00237
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024325
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024334
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024343
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024352
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024361

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00243 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [3, 1], [3, 2], [3, 3], [3, 4], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [6, 1]].all (middleFourClassificationValuesCheck 243) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00243_1_1
  · exact middle_four_classification_prefix_00243_1_2
  · exact middle_four_classification_prefix_00243_1_3
  · exact middle_four_classification_prefix_00243_1_4
  · exact middle_four_classification_prefix_00243_1_5
  · exact middle_four_classification_prefix_00243_1_6
  · exact middle_four_classification_prefix_00243_2_1
  · exact middle_four_classification_prefix_00243_2_2
  · exact middle_four_classification_prefix_00243_2_3
  · exact middle_four_classification_prefix_00243_2_4
  · exact middle_four_classification_prefix_00243_2_5
  · exact middle_four_classification_prefix_00243_3_1
  · exact middle_four_classification_prefix_00243_3_2
  · exact middle_four_classification_prefix_00243_3_3
  · exact middle_four_classification_prefix_00243_3_4
  · exact middle_four_classification_prefix_00243_4_1
  · exact middle_four_classification_prefix_00243_4_2
  · exact middle_four_classification_prefix_00243_4_3
  · exact middle_four_classification_prefix_00243_5_1
  · exact middle_four_classification_prefix_00243_5_2
  · exact middle_four_classification_prefix_00243_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
