import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00203
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020714
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020715
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020716
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020717
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020723
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020731
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020732
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020741
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020751
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020761
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0020771

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00207 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 207) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00207_1_1
  · exact middle_four_classification_prefix_00207_1_2
  · exact middle_four_classification_prefix_00207_1_3
  · exact middle_four_classification_prefix_00207_1_4
  · exact middle_four_classification_prefix_00207_1_5
  · exact middle_four_classification_prefix_00207_1_6
  · exact middle_four_classification_prefix_00207_1_7
  · exact middle_four_classification_prefix_00207_2_1
  · exact middle_four_classification_prefix_00207_2_2
  · exact middle_four_classification_prefix_00207_2_3
  · exact middle_four_classification_prefix_00207_3_1
  · exact middle_four_classification_prefix_00207_3_2
  · exact middle_four_classification_prefix_00207_4_1
  · exact middle_four_classification_prefix_00207_5_1
  · exact middle_four_classification_prefix_00207_6_1
  · exact middle_four_classification_prefix_00207_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
