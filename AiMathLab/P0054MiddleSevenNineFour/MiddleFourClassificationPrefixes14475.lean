import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes10763
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1447511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1447512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1447521

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_14475 :
    [[1, 1], [1, 2], [2, 1]].all (middleFourClassificationValuesCheck 14475) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl
  · exact middle_four_classification_prefix_14475_1_1
  · exact middle_four_classification_prefix_14475_1_2
  · exact middle_four_classification_prefix_14475_2_1

end AiMathLab.P0054.MiddleSevenNineFinite
