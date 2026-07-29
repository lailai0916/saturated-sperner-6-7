import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08363
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884317
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0884331

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08843 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 8843) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08843_1_1
  · exact middle_four_classification_prefix_08843_1_2
  · exact middle_four_classification_prefix_08843_1_3
  · exact middle_four_classification_prefix_08843_1_4
  · exact middle_four_classification_prefix_08843_1_5
  · exact middle_four_classification_prefix_08843_1_6
  · exact middle_four_classification_prefix_08843_1_7
  · exact middle_four_classification_prefix_08843_2_1
  · exact middle_four_classification_prefix_08843_2_2
  · exact middle_four_classification_prefix_08843_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
