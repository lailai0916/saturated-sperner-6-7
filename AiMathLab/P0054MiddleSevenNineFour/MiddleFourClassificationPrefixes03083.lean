import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02709
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308317
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308371

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_03083 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 3083) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_03083_1_1
  · exact middle_four_classification_prefix_03083_1_2
  · exact middle_four_classification_prefix_03083_1_3
  · exact middle_four_classification_prefix_03083_1_4
  · exact middle_four_classification_prefix_03083_1_5
  · exact middle_four_classification_prefix_03083_1_6
  · exact middle_four_classification_prefix_03083_1_7
  · exact middle_four_classification_prefix_03083_2_1
  · exact middle_four_classification_prefix_03083_2_2
  · exact middle_four_classification_prefix_03083_2_3
  · exact middle_four_classification_prefix_03083_3_1
  · exact middle_four_classification_prefix_03083_3_2
  · exact middle_four_classification_prefix_03083_4_1
  · exact middle_four_classification_prefix_03083_5_1
  · exact middle_four_classification_prefix_03083_6_1
  · exact middle_four_classification_prefix_03083_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
