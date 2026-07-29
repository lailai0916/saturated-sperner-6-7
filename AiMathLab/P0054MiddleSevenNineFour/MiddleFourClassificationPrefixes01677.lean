import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01422
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167723
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167731
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167732
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167741
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167742
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167751
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167761

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01677 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 1677) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01677_1_1
  · exact middle_four_classification_prefix_01677_1_2
  · exact middle_four_classification_prefix_01677_1_3
  · exact middle_four_classification_prefix_01677_2_1
  · exact middle_four_classification_prefix_01677_2_2
  · exact middle_four_classification_prefix_01677_2_3
  · exact middle_four_classification_prefix_01677_3_1
  · exact middle_four_classification_prefix_01677_3_2
  · exact middle_four_classification_prefix_01677_4_1
  · exact middle_four_classification_prefix_01677_4_2
  · exact middle_four_classification_prefix_01677_5_1
  · exact middle_four_classification_prefix_01677_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
