import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00243
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024532
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0024551

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00245 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 245) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00245_1_1
  · exact middle_four_classification_prefix_00245_1_2
  · exact middle_four_classification_prefix_00245_1_3
  · exact middle_four_classification_prefix_00245_2_1
  · exact middle_four_classification_prefix_00245_2_2
  · exact middle_four_classification_prefix_00245_3_1
  · exact middle_four_classification_prefix_00245_3_2
  · exact middle_four_classification_prefix_00245_4_1
  · exact middle_four_classification_prefix_00245_5_1

end AiMathLab.P0054.MiddleSevenNineFinite
