import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04238
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423961

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04239 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 4239) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04239_1_1
  · exact middle_four_classification_prefix_04239_1_2
  · exact middle_four_classification_prefix_04239_1_3
  · exact middle_four_classification_prefix_04239_2_1
  · exact middle_four_classification_prefix_04239_2_2
  · exact middle_four_classification_prefix_04239_3_1
  · exact middle_four_classification_prefix_04239_4_1
  · exact middle_four_classification_prefix_04239_5_1
  · exact middle_four_classification_prefix_04239_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
