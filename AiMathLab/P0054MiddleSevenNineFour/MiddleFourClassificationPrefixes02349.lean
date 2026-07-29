import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234961

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02349 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 2349) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02349_1_1
  · exact middle_four_classification_prefix_02349_1_2
  · exact middle_four_classification_prefix_02349_1_3
  · exact middle_four_classification_prefix_02349_2_1
  · exact middle_four_classification_prefix_02349_2_2
  · exact middle_four_classification_prefix_02349_2_3
  · exact middle_four_classification_prefix_02349_3_1
  · exact middle_four_classification_prefix_02349_3_2
  · exact middle_four_classification_prefix_02349_4_1
  · exact middle_four_classification_prefix_02349_4_2
  · exact middle_four_classification_prefix_02349_5_1
  · exact middle_four_classification_prefix_02349_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
