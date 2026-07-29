import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00251
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041011
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041012
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041013
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041014
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041015
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041016
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041017
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041021
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041022
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0041031

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00410 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [3, 1]].all (middleFourClassificationValuesCheck 410) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00410_1_1
  · exact middle_four_classification_prefix_00410_1_2
  · exact middle_four_classification_prefix_00410_1_3
  · exact middle_four_classification_prefix_00410_1_4
  · exact middle_four_classification_prefix_00410_1_5
  · exact middle_four_classification_prefix_00410_1_6
  · exact middle_four_classification_prefix_00410_1_7
  · exact middle_four_classification_prefix_00410_2_1
  · exact middle_four_classification_prefix_00410_2_2
  · exact middle_four_classification_prefix_00410_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
