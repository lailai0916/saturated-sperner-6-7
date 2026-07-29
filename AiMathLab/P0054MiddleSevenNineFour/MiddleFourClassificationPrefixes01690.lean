import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00824
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169011
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169012
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169021
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169022
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169031
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169032
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169041
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169042
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169051
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169052
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0169061

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01690 :
    [[1, 1], [1, 2], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [5, 2], [6, 1]].all (middleFourClassificationValuesCheck 1690) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01690_1_1
  · exact middle_four_classification_prefix_01690_1_2
  · exact middle_four_classification_prefix_01690_2_1
  · exact middle_four_classification_prefix_01690_2_2
  · exact middle_four_classification_prefix_01690_3_1
  · exact middle_four_classification_prefix_01690_3_2
  · exact middle_four_classification_prefix_01690_4_1
  · exact middle_four_classification_prefix_01690_4_2
  · exact middle_four_classification_prefix_01690_5_1
  · exact middle_four_classification_prefix_01690_5_2
  · exact middle_four_classification_prefix_01690_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
