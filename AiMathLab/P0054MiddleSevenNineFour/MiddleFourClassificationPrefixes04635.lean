import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463532
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463542
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463551
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463552
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0463561

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04635 :
    [[1, 1], [1, 2], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [5, 2], [6, 1]].all (middleFourClassificationValuesCheck 4635) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04635_1_1
  · exact middle_four_classification_prefix_04635_1_2
  · exact middle_four_classification_prefix_04635_2_1
  · exact middle_four_classification_prefix_04635_2_2
  · exact middle_four_classification_prefix_04635_3_1
  · exact middle_four_classification_prefix_04635_3_2
  · exact middle_four_classification_prefix_04635_4_1
  · exact middle_four_classification_prefix_04635_4_2
  · exact middle_four_classification_prefix_04635_5_1
  · exact middle_four_classification_prefix_04635_5_2
  · exact middle_four_classification_prefix_04635_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
