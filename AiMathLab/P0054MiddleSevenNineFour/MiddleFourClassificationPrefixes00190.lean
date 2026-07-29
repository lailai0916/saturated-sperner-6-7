import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00189
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0019011
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0019012
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0019021
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0019022
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0019031
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0019041
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0019051

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00190 :
    [[1, 1], [1, 2], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 190) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00190_1_1
  · exact middle_four_classification_prefix_00190_1_2
  · exact middle_four_classification_prefix_00190_2_1
  · exact middle_four_classification_prefix_00190_2_2
  · exact middle_four_classification_prefix_00190_3_1
  · exact middle_four_classification_prefix_00190_4_1
  · exact middle_four_classification_prefix_00190_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
