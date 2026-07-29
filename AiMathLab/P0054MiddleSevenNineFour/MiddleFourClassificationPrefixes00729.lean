import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00653
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072915
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072916
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0072961

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00729 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 729) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00729_1_1
  · exact middle_four_classification_prefix_00729_1_2
  · exact middle_four_classification_prefix_00729_1_3
  · exact middle_four_classification_prefix_00729_1_4
  · exact middle_four_classification_prefix_00729_1_5
  · exact middle_four_classification_prefix_00729_1_6
  · exact middle_four_classification_prefix_00729_2_1
  · exact middle_four_classification_prefix_00729_2_2
  · exact middle_four_classification_prefix_00729_2_3
  · exact middle_four_classification_prefix_00729_3_1
  · exact middle_four_classification_prefix_00729_3_2
  · exact middle_four_classification_prefix_00729_4_1
  · exact middle_four_classification_prefix_00729_5_1
  · exact middle_four_classification_prefix_00729_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
