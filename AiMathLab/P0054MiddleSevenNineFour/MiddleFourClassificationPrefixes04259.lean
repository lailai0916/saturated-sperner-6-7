import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes03083
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425933
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425943
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425952
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425953
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425961
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425962
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425971

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04259 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 4259) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04259_1_1
  · exact middle_four_classification_prefix_04259_1_2
  · exact middle_four_classification_prefix_04259_1_3
  · exact middle_four_classification_prefix_04259_2_1
  · exact middle_four_classification_prefix_04259_2_2
  · exact middle_four_classification_prefix_04259_2_3
  · exact middle_four_classification_prefix_04259_3_1
  · exact middle_four_classification_prefix_04259_3_2
  · exact middle_four_classification_prefix_04259_3_3
  · exact middle_four_classification_prefix_04259_4_1
  · exact middle_four_classification_prefix_04259_4_2
  · exact middle_four_classification_prefix_04259_4_3
  · exact middle_four_classification_prefix_04259_5_1
  · exact middle_four_classification_prefix_04259_5_2
  · exact middle_four_classification_prefix_04259_5_3
  · exact middle_four_classification_prefix_04259_6_1
  · exact middle_four_classification_prefix_04259_6_2
  · exact middle_four_classification_prefix_04259_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
