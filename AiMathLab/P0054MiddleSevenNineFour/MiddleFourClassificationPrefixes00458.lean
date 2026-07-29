import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00395
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045814
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045815
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045816
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045817
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045823
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045831
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045832
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045841
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045851
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045861
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0045871

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00458 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 458) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00458_1_1
  · exact middle_four_classification_prefix_00458_1_2
  · exact middle_four_classification_prefix_00458_1_3
  · exact middle_four_classification_prefix_00458_1_4
  · exact middle_four_classification_prefix_00458_1_5
  · exact middle_four_classification_prefix_00458_1_6
  · exact middle_four_classification_prefix_00458_1_7
  · exact middle_four_classification_prefix_00458_2_1
  · exact middle_four_classification_prefix_00458_2_2
  · exact middle_four_classification_prefix_00458_2_3
  · exact middle_four_classification_prefix_00458_3_1
  · exact middle_four_classification_prefix_00458_3_2
  · exact middle_four_classification_prefix_00458_4_1
  · exact middle_four_classification_prefix_00458_5_1
  · exact middle_four_classification_prefix_00458_6_1
  · exact middle_four_classification_prefix_00458_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
