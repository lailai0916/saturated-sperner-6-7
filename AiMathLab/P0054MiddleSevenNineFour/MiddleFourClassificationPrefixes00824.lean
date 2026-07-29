import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00729
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082411
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082412
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082413
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082421
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082422
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082423
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082431
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082432
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082433
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082441
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082442
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082443
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082451
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082452
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082453
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082461
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082462
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0082471

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00824 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 824) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00824_1_1
  · exact middle_four_classification_prefix_00824_1_2
  · exact middle_four_classification_prefix_00824_1_3
  · exact middle_four_classification_prefix_00824_2_1
  · exact middle_four_classification_prefix_00824_2_2
  · exact middle_four_classification_prefix_00824_2_3
  · exact middle_four_classification_prefix_00824_3_1
  · exact middle_four_classification_prefix_00824_3_2
  · exact middle_four_classification_prefix_00824_3_3
  · exact middle_four_classification_prefix_00824_4_1
  · exact middle_four_classification_prefix_00824_4_2
  · exact middle_four_classification_prefix_00824_4_3
  · exact middle_four_classification_prefix_00824_5_1
  · exact middle_four_classification_prefix_00824_5_2
  · exact middle_four_classification_prefix_00824_5_3
  · exact middle_four_classification_prefix_00824_6_1
  · exact middle_four_classification_prefix_00824_6_2
  · exact middle_four_classification_prefix_00824_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
