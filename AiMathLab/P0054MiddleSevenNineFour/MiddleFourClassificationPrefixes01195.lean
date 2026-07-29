import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01193
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119515
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119516
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119531

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01195 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 1195) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01195_1_1
  · exact middle_four_classification_prefix_01195_1_2
  · exact middle_four_classification_prefix_01195_1_3
  · exact middle_four_classification_prefix_01195_1_4
  · exact middle_four_classification_prefix_01195_1_5
  · exact middle_four_classification_prefix_01195_1_6
  · exact middle_four_classification_prefix_01195_2_1
  · exact middle_four_classification_prefix_01195_2_2
  · exact middle_four_classification_prefix_01195_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
