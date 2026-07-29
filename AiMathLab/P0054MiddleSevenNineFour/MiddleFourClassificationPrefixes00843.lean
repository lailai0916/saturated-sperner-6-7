import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00824
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0084351

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00843 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 1], [2, 2], [2, 3], [2, 4], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1]].all (middleFourClassificationValuesCheck 843) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00843_1_1
  · exact middle_four_classification_prefix_00843_1_2
  · exact middle_four_classification_prefix_00843_1_3
  · exact middle_four_classification_prefix_00843_1_4
  · exact middle_four_classification_prefix_00843_1_5
  · exact middle_four_classification_prefix_00843_2_1
  · exact middle_four_classification_prefix_00843_2_2
  · exact middle_four_classification_prefix_00843_2_3
  · exact middle_four_classification_prefix_00843_2_4
  · exact middle_four_classification_prefix_00843_3_1
  · exact middle_four_classification_prefix_00843_3_2
  · exact middle_four_classification_prefix_00843_3_3
  · exact middle_four_classification_prefix_00843_4_1
  · exact middle_four_classification_prefix_00843_4_2
  · exact middle_four_classification_prefix_00843_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
