import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01449
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219551
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219561
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0219571

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02195 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 2195) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02195_1_1
  · exact middle_four_classification_prefix_02195_1_2
  · exact middle_four_classification_prefix_02195_1_3
  · exact middle_four_classification_prefix_02195_2_1
  · exact middle_four_classification_prefix_02195_2_2
  · exact middle_four_classification_prefix_02195_3_1
  · exact middle_four_classification_prefix_02195_4_1
  · exact middle_four_classification_prefix_02195_5_1
  · exact middle_four_classification_prefix_02195_6_1
  · exact middle_four_classification_prefix_02195_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
