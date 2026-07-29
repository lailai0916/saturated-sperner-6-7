import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes08333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849116
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849123
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849124
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849125

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_08491 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5]].all (middleFourClassificationValuesCheck 8491) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_08491_1_1
  · exact middle_four_classification_prefix_08491_1_2
  · exact middle_four_classification_prefix_08491_1_3
  · exact middle_four_classification_prefix_08491_1_4
  · exact middle_four_classification_prefix_08491_1_5
  · exact middle_four_classification_prefix_08491_1_6
  · exact middle_four_classification_prefix_08491_2_1
  · exact middle_four_classification_prefix_08491_2_2
  · exact middle_four_classification_prefix_08491_2_3
  · exact middle_four_classification_prefix_08491_2_4
  · exact middle_four_classification_prefix_08491_2_5

end AiMathLab.P0054.MiddleSevenNineFinite
