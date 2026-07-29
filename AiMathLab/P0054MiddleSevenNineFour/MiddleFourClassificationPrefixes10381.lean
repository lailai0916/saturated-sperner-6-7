import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes10379
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1038111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1038121

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_10381 :
    [[1, 1], [2, 1]].all (middleFourClassificationValuesCheck 10381) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl
  · exact middle_four_classification_prefix_10381_1_1
  · exact middle_four_classification_prefix_10381_2_1

end AiMathLab.P0054.MiddleSevenNineFinite
