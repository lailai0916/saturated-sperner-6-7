import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01195
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0120351

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01203 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 1], [2, 2], [2, 3], [2, 4], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1]].all (middleFourClassificationValuesCheck 1203) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01203_1_1
  · exact middle_four_classification_prefix_01203_1_2
  · exact middle_four_classification_prefix_01203_1_3
  · exact middle_four_classification_prefix_01203_1_4
  · exact middle_four_classification_prefix_01203_1_5
  · exact middle_four_classification_prefix_01203_2_1
  · exact middle_four_classification_prefix_01203_2_2
  · exact middle_four_classification_prefix_01203_2_3
  · exact middle_four_classification_prefix_01203_2_4
  · exact middle_four_classification_prefix_01203_3_1
  · exact middle_four_classification_prefix_01203_3_2
  · exact middle_four_classification_prefix_01203_3_3
  · exact middle_four_classification_prefix_01203_4_1
  · exact middle_four_classification_prefix_01203_4_2
  · exact middle_four_classification_prefix_01203_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
