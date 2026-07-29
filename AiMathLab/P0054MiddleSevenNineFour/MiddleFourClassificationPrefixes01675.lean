import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01419
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167515
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167516
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167517
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167523
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0167541

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01675 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1], [4, 1]].all (middleFourClassificationValuesCheck 1675) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01675_1_1
  · exact middle_four_classification_prefix_01675_1_2
  · exact middle_four_classification_prefix_01675_1_3
  · exact middle_four_classification_prefix_01675_1_4
  · exact middle_four_classification_prefix_01675_1_5
  · exact middle_four_classification_prefix_01675_1_6
  · exact middle_four_classification_prefix_01675_1_7
  · exact middle_four_classification_prefix_01675_2_1
  · exact middle_four_classification_prefix_01675_2_2
  · exact middle_four_classification_prefix_01675_2_3
  · exact middle_four_classification_prefix_01675_3_1
  · exact middle_four_classification_prefix_01675_4_1

end AiMathLab.P0054.MiddleSevenNineFinite
