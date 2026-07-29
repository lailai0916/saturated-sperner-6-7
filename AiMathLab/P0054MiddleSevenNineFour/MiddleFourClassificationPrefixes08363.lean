import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836314
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836315
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836316
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836317
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0836331

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08363 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 8363) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08363_1_1
  · exact middle_four_classification_prefix_08363_1_2
  · exact middle_four_classification_prefix_08363_1_3
  · exact middle_four_classification_prefix_08363_1_4
  · exact middle_four_classification_prefix_08363_1_5
  · exact middle_four_classification_prefix_08363_1_6
  · exact middle_four_classification_prefix_08363_1_7
  · exact middle_four_classification_prefix_08363_2_1
  · exact middle_four_classification_prefix_08363_2_2
  · exact middle_four_classification_prefix_08363_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
