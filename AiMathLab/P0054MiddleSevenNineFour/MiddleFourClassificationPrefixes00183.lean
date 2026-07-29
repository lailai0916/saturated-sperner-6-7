import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00179
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0018351

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00183 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [2, 1], [2, 2], [2, 3], [2, 4], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1]].all (middleFourClassificationValuesCheck 183) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00183_1_1
  · exact middle_four_classification_prefix_00183_1_2
  · exact middle_four_classification_prefix_00183_1_3
  · exact middle_four_classification_prefix_00183_1_4
  · exact middle_four_classification_prefix_00183_1_5
  · exact middle_four_classification_prefix_00183_2_1
  · exact middle_four_classification_prefix_00183_2_2
  · exact middle_four_classification_prefix_00183_2_3
  · exact middle_four_classification_prefix_00183_2_4
  · exact middle_four_classification_prefix_00183_3_1
  · exact middle_four_classification_prefix_00183_3_2
  · exact middle_four_classification_prefix_00183_3_3
  · exact middle_four_classification_prefix_00183_4_1
  · exact middle_four_classification_prefix_00183_4_2
  · exact middle_four_classification_prefix_00183_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
