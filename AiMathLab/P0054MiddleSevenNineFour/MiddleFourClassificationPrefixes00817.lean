import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00681
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081723
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081731
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081732
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081733
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081741
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081742
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081743
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081751
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081752
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081753
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081761
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081762
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081771

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00817 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 817) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00817_1_1
  · exact middle_four_classification_prefix_00817_1_2
  · exact middle_four_classification_prefix_00817_1_3
  · exact middle_four_classification_prefix_00817_2_1
  · exact middle_four_classification_prefix_00817_2_2
  · exact middle_four_classification_prefix_00817_2_3
  · exact middle_four_classification_prefix_00817_3_1
  · exact middle_four_classification_prefix_00817_3_2
  · exact middle_four_classification_prefix_00817_3_3
  · exact middle_four_classification_prefix_00817_4_1
  · exact middle_four_classification_prefix_00817_4_2
  · exact middle_four_classification_prefix_00817_4_3
  · exact middle_four_classification_prefix_00817_5_1
  · exact middle_four_classification_prefix_00817_5_2
  · exact middle_four_classification_prefix_00817_5_3
  · exact middle_four_classification_prefix_00817_6_1
  · exact middle_four_classification_prefix_00817_6_2
  · exact middle_four_classification_prefix_00817_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
