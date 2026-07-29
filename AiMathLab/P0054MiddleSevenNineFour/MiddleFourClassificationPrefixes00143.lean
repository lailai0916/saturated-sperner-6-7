import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1037931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014317
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014318
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014324
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014371
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0014381

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00143 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [2, 1], [2, 2], [2, 3], [2, 4], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [6, 1], [7, 1], [8, 1]].all (middleFourClassificationValuesCheck 143) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00143_1_1
  · exact middle_four_classification_prefix_00143_1_2
  · exact middle_four_classification_prefix_00143_1_3
  · exact middle_four_classification_prefix_00143_1_4
  · exact middle_four_classification_prefix_00143_1_5
  · exact middle_four_classification_prefix_00143_1_6
  · exact middle_four_classification_prefix_00143_1_7
  · exact middle_four_classification_prefix_00143_1_8
  · exact middle_four_classification_prefix_00143_2_1
  · exact middle_four_classification_prefix_00143_2_2
  · exact middle_four_classification_prefix_00143_2_3
  · exact middle_four_classification_prefix_00143_2_4
  · exact middle_four_classification_prefix_00143_3_1
  · exact middle_four_classification_prefix_00143_3_2
  · exact middle_four_classification_prefix_00143_4_1
  · exact middle_four_classification_prefix_00143_4_2
  · exact middle_four_classification_prefix_00143_5_1
  · exact middle_four_classification_prefix_00143_6_1
  · exact middle_four_classification_prefix_00143_7_1
  · exact middle_four_classification_prefix_00143_8_1

end AiMathLab.P0054.MiddleSevenNineFinite
