import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00251
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0025311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0025312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0025321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0025331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0025341

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00253 :
    [[1, 1], [1, 2], [2, 1], [3, 1], [4, 1]].all (middleFourClassificationValuesCheck 253) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00253_1_1
  · exact middle_four_classification_prefix_00253_1_2
  · exact middle_four_classification_prefix_00253_2_1
  · exact middle_four_classification_prefix_00253_3_1
  · exact middle_four_classification_prefix_00253_4_1

end AiMathLab.P0054.MiddleSevenNineFinite
