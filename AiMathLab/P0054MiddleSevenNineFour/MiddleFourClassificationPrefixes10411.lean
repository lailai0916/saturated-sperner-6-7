import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes10403
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1041111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1041112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1041113

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_10411 :
    [[1, 1], [1, 2], [1, 3]].all (middleFourClassificationValuesCheck 10411) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl
  · exact middle_four_classification_prefix_10411_1_1
  · exact middle_four_classification_prefix_10411_1_2
  · exact middle_four_classification_prefix_10411_1_3

end AiMathLab.P0054.MiddleSevenNineFinite
