import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00410
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065352
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0065371

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00653 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1], [5, 2], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 653) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00653_1_1
  · exact middle_four_classification_prefix_00653_1_2
  · exact middle_four_classification_prefix_00653_1_3
  · exact middle_four_classification_prefix_00653_1_4
  · exact middle_four_classification_prefix_00653_2_1
  · exact middle_four_classification_prefix_00653_2_2
  · exact middle_four_classification_prefix_00653_2_3
  · exact middle_four_classification_prefix_00653_3_1
  · exact middle_four_classification_prefix_00653_3_2
  · exact middle_four_classification_prefix_00653_3_3
  · exact middle_four_classification_prefix_00653_4_1
  · exact middle_four_classification_prefix_00653_4_2
  · exact middle_four_classification_prefix_00653_5_1
  · exact middle_four_classification_prefix_00653_5_2
  · exact middle_four_classification_prefix_00653_6_1
  · exact middle_four_classification_prefix_00653_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
