import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00817
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144952
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0144961

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01449 :
    [[1, 1], [1, 2], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [5, 2], [6, 1]].all (middleFourClassificationValuesCheck 1449) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01449_1_1
  · exact middle_four_classification_prefix_01449_1_2
  · exact middle_four_classification_prefix_01449_2_1
  · exact middle_four_classification_prefix_01449_2_2
  · exact middle_four_classification_prefix_01449_3_1
  · exact middle_four_classification_prefix_01449_3_2
  · exact middle_four_classification_prefix_01449_4_1
  · exact middle_four_classification_prefix_01449_4_2
  · exact middle_four_classification_prefix_01449_5_1
  · exact middle_four_classification_prefix_01449_5_2
  · exact middle_four_classification_prefix_01449_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
