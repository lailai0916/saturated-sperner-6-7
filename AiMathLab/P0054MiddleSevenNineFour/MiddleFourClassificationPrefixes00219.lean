import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00207
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021961
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021971

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00219 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 219) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00219_1_1
  · exact middle_four_classification_prefix_00219_1_2
  · exact middle_four_classification_prefix_00219_1_3
  · exact middle_four_classification_prefix_00219_1_4
  · exact middle_four_classification_prefix_00219_2_1
  · exact middle_four_classification_prefix_00219_2_2
  · exact middle_four_classification_prefix_00219_3_1
  · exact middle_four_classification_prefix_00219_3_2
  · exact middle_four_classification_prefix_00219_4_1
  · exact middle_four_classification_prefix_00219_5_1
  · exact middle_four_classification_prefix_00219_6_1
  · exact middle_four_classification_prefix_00219_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
