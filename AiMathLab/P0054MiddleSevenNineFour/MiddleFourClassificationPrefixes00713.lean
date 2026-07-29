import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00651
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071317
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0071371

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00713 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 713) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00713_1_1
  · exact middle_four_classification_prefix_00713_1_2
  · exact middle_four_classification_prefix_00713_1_3
  · exact middle_four_classification_prefix_00713_1_4
  · exact middle_four_classification_prefix_00713_1_5
  · exact middle_four_classification_prefix_00713_1_6
  · exact middle_four_classification_prefix_00713_1_7
  · exact middle_four_classification_prefix_00713_2_1
  · exact middle_four_classification_prefix_00713_2_2
  · exact middle_four_classification_prefix_00713_2_3
  · exact middle_four_classification_prefix_00713_3_1
  · exact middle_four_classification_prefix_00713_3_2
  · exact middle_four_classification_prefix_00713_4_1
  · exact middle_four_classification_prefix_00713_5_1
  · exact middle_four_classification_prefix_00713_6_1
  · exact middle_four_classification_prefix_00713_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
