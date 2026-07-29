import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02582
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423831

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04238 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 4238) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04238_1_1
  · exact middle_four_classification_prefix_04238_1_2
  · exact middle_four_classification_prefix_04238_1_3
  · exact middle_four_classification_prefix_04238_2_1
  · exact middle_four_classification_prefix_04238_2_2
  · exact middle_four_classification_prefix_04238_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
