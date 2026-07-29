import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02590
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0270961

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02709 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 2709) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02709_1_1
  · exact middle_four_classification_prefix_02709_1_2
  · exact middle_four_classification_prefix_02709_1_3
  · exact middle_four_classification_prefix_02709_2_1
  · exact middle_four_classification_prefix_02709_2_2
  · exact middle_four_classification_prefix_02709_2_3
  · exact middle_four_classification_prefix_02709_3_1
  · exact middle_four_classification_prefix_02709_3_2
  · exact middle_four_classification_prefix_02709_4_1
  · exact middle_four_classification_prefix_02709_4_2
  · exact middle_four_classification_prefix_02709_5_1
  · exact middle_four_classification_prefix_02709_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
