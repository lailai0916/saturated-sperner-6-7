import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes06411
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833915
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833916
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833917
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833924
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833925
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833926
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833933
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833934
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0833935

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08339 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [2, 6], [3, 1], [3, 2], [3, 3], [3, 4], [3, 5]].all (middleFourClassificationValuesCheck 8339) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08339_1_1
  · exact middle_four_classification_prefix_08339_1_2
  · exact middle_four_classification_prefix_08339_1_3
  · exact middle_four_classification_prefix_08339_1_4
  · exact middle_four_classification_prefix_08339_1_5
  · exact middle_four_classification_prefix_08339_1_6
  · exact middle_four_classification_prefix_08339_1_7
  · exact middle_four_classification_prefix_08339_2_1
  · exact middle_four_classification_prefix_08339_2_2
  · exact middle_four_classification_prefix_08339_2_3
  · exact middle_four_classification_prefix_08339_2_4
  · exact middle_four_classification_prefix_08339_2_5
  · exact middle_four_classification_prefix_08339_2_6
  · exact middle_four_classification_prefix_08339_3_1
  · exact middle_four_classification_prefix_08339_3_2
  · exact middle_four_classification_prefix_08339_3_3
  · exact middle_four_classification_prefix_08339_3_4
  · exact middle_four_classification_prefix_08339_3_5

end AiMathLab.P0054.MiddleSevenNineFinite
