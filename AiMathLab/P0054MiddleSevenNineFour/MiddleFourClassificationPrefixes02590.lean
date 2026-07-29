import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02470
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259011
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259012
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259013
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259021
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259022
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259023
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259031
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259032
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259041
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259042
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259051
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0259061

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02590 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 2590) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02590_1_1
  · exact middle_four_classification_prefix_02590_1_2
  · exact middle_four_classification_prefix_02590_1_3
  · exact middle_four_classification_prefix_02590_2_1
  · exact middle_four_classification_prefix_02590_2_2
  · exact middle_four_classification_prefix_02590_2_3
  · exact middle_four_classification_prefix_02590_3_1
  · exact middle_four_classification_prefix_02590_3_2
  · exact middle_four_classification_prefix_02590_4_1
  · exact middle_four_classification_prefix_02590_4_2
  · exact middle_four_classification_prefix_02590_5_1
  · exact middle_four_classification_prefix_02590_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
