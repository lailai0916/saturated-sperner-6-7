import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00398
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049011
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049012
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049013
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049014
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049015
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049016
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049021
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049022
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049023
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049031
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049032
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049041
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049051
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0049061

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00490 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 490) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00490_1_1
  · exact middle_four_classification_prefix_00490_1_2
  · exact middle_four_classification_prefix_00490_1_3
  · exact middle_four_classification_prefix_00490_1_4
  · exact middle_four_classification_prefix_00490_1_5
  · exact middle_four_classification_prefix_00490_1_6
  · exact middle_four_classification_prefix_00490_2_1
  · exact middle_four_classification_prefix_00490_2_2
  · exact middle_four_classification_prefix_00490_2_3
  · exact middle_four_classification_prefix_00490_3_1
  · exact middle_four_classification_prefix_00490_3_2
  · exact middle_four_classification_prefix_00490_4_1
  · exact middle_four_classification_prefix_00490_5_1
  · exact middle_four_classification_prefix_00490_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
