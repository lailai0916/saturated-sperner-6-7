import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00158
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017352
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017371

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00173 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1], [5, 2], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 173) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00173_1_1
  · exact middle_four_classification_prefix_00173_1_2
  · exact middle_four_classification_prefix_00173_1_3
  · exact middle_four_classification_prefix_00173_1_4
  · exact middle_four_classification_prefix_00173_2_1
  · exact middle_four_classification_prefix_00173_2_2
  · exact middle_four_classification_prefix_00173_2_3
  · exact middle_four_classification_prefix_00173_3_1
  · exact middle_four_classification_prefix_00173_3_2
  · exact middle_four_classification_prefix_00173_3_3
  · exact middle_four_classification_prefix_00173_4_1
  · exact middle_four_classification_prefix_00173_4_2
  · exact middle_four_classification_prefix_00173_5_1
  · exact middle_four_classification_prefix_00173_5_2
  · exact middle_four_classification_prefix_00173_6_1
  · exact middle_four_classification_prefix_00173_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
