import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02195
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224714
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224715
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224716
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224723
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224731
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224732
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224741
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224751
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0224761

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02247 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 2247) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02247_1_1
  · exact middle_four_classification_prefix_02247_1_2
  · exact middle_four_classification_prefix_02247_1_3
  · exact middle_four_classification_prefix_02247_1_4
  · exact middle_four_classification_prefix_02247_1_5
  · exact middle_four_classification_prefix_02247_1_6
  · exact middle_four_classification_prefix_02247_2_1
  · exact middle_four_classification_prefix_02247_2_2
  · exact middle_four_classification_prefix_02247_2_3
  · exact middle_four_classification_prefix_02247_3_1
  · exact middle_four_classification_prefix_02247_3_2
  · exact middle_four_classification_prefix_02247_4_1
  · exact middle_four_classification_prefix_02247_5_1
  · exact middle_four_classification_prefix_02247_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
