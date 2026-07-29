import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00179
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039523
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039532
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039551
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039561
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039571
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039581

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00395 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1], [8, 1]].all (middleFourClassificationValuesCheck 395) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00395_1_1
  · exact middle_four_classification_prefix_00395_1_2
  · exact middle_four_classification_prefix_00395_1_3
  · exact middle_four_classification_prefix_00395_1_4
  · exact middle_four_classification_prefix_00395_2_1
  · exact middle_four_classification_prefix_00395_2_2
  · exact middle_four_classification_prefix_00395_2_3
  · exact middle_four_classification_prefix_00395_3_1
  · exact middle_four_classification_prefix_00395_3_2
  · exact middle_four_classification_prefix_00395_4_1
  · exact middle_four_classification_prefix_00395_5_1
  · exact middle_four_classification_prefix_00395_6_1
  · exact middle_four_classification_prefix_00395_7_1
  · exact middle_four_classification_prefix_00395_8_1

end AiMathLab.P0054.MiddleSevenNineFinite
