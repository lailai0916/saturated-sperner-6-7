import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01167
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141961
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0141971

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01419 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 1419) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01419_1_1
  · exact middle_four_classification_prefix_01419_1_2
  · exact middle_four_classification_prefix_01419_1_3
  · exact middle_four_classification_prefix_01419_1_4
  · exact middle_four_classification_prefix_01419_2_1
  · exact middle_four_classification_prefix_01419_2_2
  · exact middle_four_classification_prefix_01419_3_1
  · exact middle_four_classification_prefix_01419_3_2
  · exact middle_four_classification_prefix_01419_4_1
  · exact middle_four_classification_prefix_01419_5_1
  · exact middle_four_classification_prefix_01419_6_1
  · exact middle_four_classification_prefix_01419_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
