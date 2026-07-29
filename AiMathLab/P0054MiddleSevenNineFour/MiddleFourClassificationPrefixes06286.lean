import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes06283
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0628611
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0628621

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_06286 :
    [[1, 1], [2, 1]].all (middleFourClassificationValuesCheck 6286) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl
  · exact middle_four_classification_prefix_06286_1_1
  · exact middle_four_classification_prefix_06286_2_1

end AiMathLab.P0054.MiddleSevenNineFinite
