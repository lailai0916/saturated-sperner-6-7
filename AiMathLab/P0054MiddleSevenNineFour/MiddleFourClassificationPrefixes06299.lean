import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes06291
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0629931

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_06299 :
    [[1, 1], [2, 1], [3, 1]].all (middleFourClassificationValuesCheck 6299) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl
  · exact middle_four_classification_prefix_06299_1_1
  · exact middle_four_classification_prefix_06299_2_1
  · exact middle_four_classification_prefix_06299_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
