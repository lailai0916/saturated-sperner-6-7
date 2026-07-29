import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08339
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845915
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845916
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845917
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845924
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845925
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845926
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845933
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845934
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0845935

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08459 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [2, 6], [3, 1], [3, 2], [3, 3], [3, 4], [3, 5]].all (middleFourClassificationValuesCheck 8459) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08459_1_1
  · exact middle_four_classification_prefix_08459_1_2
  · exact middle_four_classification_prefix_08459_1_3
  · exact middle_four_classification_prefix_08459_1_4
  · exact middle_four_classification_prefix_08459_1_5
  · exact middle_four_classification_prefix_08459_1_6
  · exact middle_four_classification_prefix_08459_1_7
  · exact middle_four_classification_prefix_08459_2_1
  · exact middle_four_classification_prefix_08459_2_2
  · exact middle_four_classification_prefix_08459_2_3
  · exact middle_four_classification_prefix_08459_2_4
  · exact middle_four_classification_prefix_08459_2_5
  · exact middle_four_classification_prefix_08459_2_6
  · exact middle_four_classification_prefix_08459_3_1
  · exact middle_four_classification_prefix_08459_3_2
  · exact middle_four_classification_prefix_08459_3_3
  · exact middle_four_classification_prefix_08459_3_4
  · exact middle_four_classification_prefix_08459_3_5

end AiMathLab.P0054.MiddleSevenNineFinite
