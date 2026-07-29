import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02582
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258814
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258815
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258816
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258817
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258823
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0258831

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02588 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1]].all (middleFourClassificationValuesCheck 2588) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02588_1_1
  · exact middle_four_classification_prefix_02588_1_2
  · exact middle_four_classification_prefix_02588_1_3
  · exact middle_four_classification_prefix_02588_1_4
  · exact middle_four_classification_prefix_02588_1_5
  · exact middle_four_classification_prefix_02588_1_6
  · exact middle_four_classification_prefix_02588_1_7
  · exact middle_four_classification_prefix_02588_2_1
  · exact middle_four_classification_prefix_02588_2_2
  · exact middle_four_classification_prefix_02588_2_3
  · exact middle_four_classification_prefix_02588_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
