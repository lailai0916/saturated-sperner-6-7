import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02571
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258211
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258212
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258213
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258221
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258222
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258223
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258231
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258232
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258233
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258241
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258242
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258243
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258251
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258252
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258253
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258261
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258262
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258271

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02582 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 2582) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02582_1_1
  · exact middle_four_classification_prefix_02582_1_2
  · exact middle_four_classification_prefix_02582_1_3
  · exact middle_four_classification_prefix_02582_2_1
  · exact middle_four_classification_prefix_02582_2_2
  · exact middle_four_classification_prefix_02582_2_3
  · exact middle_four_classification_prefix_02582_3_1
  · exact middle_four_classification_prefix_02582_3_2
  · exact middle_four_classification_prefix_02582_3_3
  · exact middle_four_classification_prefix_02582_4_1
  · exact middle_four_classification_prefix_02582_4_2
  · exact middle_four_classification_prefix_02582_4_3
  · exact middle_four_classification_prefix_02582_5_1
  · exact middle_four_classification_prefix_02582_5_2
  · exact middle_four_classification_prefix_02582_5_3
  · exact middle_four_classification_prefix_02582_6_1
  · exact middle_four_classification_prefix_02582_6_2
  · exact middle_four_classification_prefix_02582_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
