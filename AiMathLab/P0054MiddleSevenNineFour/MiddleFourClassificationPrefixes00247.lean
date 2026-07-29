import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00245
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024714
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024723
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024731
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024732
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024741

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00247 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1]].all (middleFourClassificationValuesCheck 247) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00247_1_1
  · exact middle_four_classification_prefix_00247_1_2
  · exact middle_four_classification_prefix_00247_1_3
  · exact middle_four_classification_prefix_00247_1_4
  · exact middle_four_classification_prefix_00247_2_1
  · exact middle_four_classification_prefix_00247_2_2
  · exact middle_four_classification_prefix_00247_2_3
  · exact middle_four_classification_prefix_00247_3_1
  · exact middle_four_classification_prefix_00247_3_2
  · exact middle_four_classification_prefix_00247_4_1

end AiMathLab.P0054.MiddleSevenNineFinite
