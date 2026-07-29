import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes06291
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0641111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0641112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0641121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0641131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0641141
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0641151
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0641161

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_06411 :
    [[1, 1], [1, 2], [2, 1], [3, 1], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 6411) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_06411_1_1
  · exact middle_four_classification_prefix_06411_1_2
  · exact middle_four_classification_prefix_06411_2_1
  · exact middle_four_classification_prefix_06411_3_1
  · exact middle_four_classification_prefix_06411_4_1
  · exact middle_four_classification_prefix_06411_5_1
  · exact middle_four_classification_prefix_06411_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
