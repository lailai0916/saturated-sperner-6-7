import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04259
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450611
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450612
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450613
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450614
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450615
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450616
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0450621

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04506 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1]].all (middleFourClassificationValuesCheck 4506) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04506_1_1
  · exact middle_four_classification_prefix_04506_1_2
  · exact middle_four_classification_prefix_04506_1_3
  · exact middle_four_classification_prefix_04506_1_4
  · exact middle_four_classification_prefix_04506_1_5
  · exact middle_four_classification_prefix_04506_1_6
  · exact middle_four_classification_prefix_04506_2_1

end AiMathLab.P0054.MiddleSevenNineFinite
