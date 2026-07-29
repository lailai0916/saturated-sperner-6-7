import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02349
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247011
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247012
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247013
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247021
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247022
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247023
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247031
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247032
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247041
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247042
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247051
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0247061

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02470 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 2470) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02470_1_1
  · exact middle_four_classification_prefix_02470_1_2
  · exact middle_four_classification_prefix_02470_1_3
  · exact middle_four_classification_prefix_02470_2_1
  · exact middle_four_classification_prefix_02470_2_2
  · exact middle_four_classification_prefix_02470_2_3
  · exact middle_four_classification_prefix_02470_3_1
  · exact middle_four_classification_prefix_02470_3_2
  · exact middle_four_classification_prefix_02470_4_1
  · exact middle_four_classification_prefix_02470_4_2
  · exact middle_four_classification_prefix_02470_5_1
  · exact middle_four_classification_prefix_02470_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
