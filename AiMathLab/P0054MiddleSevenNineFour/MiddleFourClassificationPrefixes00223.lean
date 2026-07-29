import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849125
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0022311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0022312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0022313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0022321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0022322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0022331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0022341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0022351

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00223 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 223) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00223_1_1
  · exact middle_four_classification_prefix_00223_1_2
  · exact middle_four_classification_prefix_00223_1_3
  · exact middle_four_classification_prefix_00223_2_1
  · exact middle_four_classification_prefix_00223_2_2
  · exact middle_four_classification_prefix_00223_3_1
  · exact middle_four_classification_prefix_00223_4_1
  · exact middle_four_classification_prefix_00223_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
