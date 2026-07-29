import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00222
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023515
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023516
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023517
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023523
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0023541

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00235 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1], [4, 1]].all (middleFourClassificationValuesCheck 235) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00235_1_1
  · exact middle_four_classification_prefix_00235_1_2
  · exact middle_four_classification_prefix_00235_1_3
  · exact middle_four_classification_prefix_00235_1_4
  · exact middle_four_classification_prefix_00235_1_5
  · exact middle_four_classification_prefix_00235_1_6
  · exact middle_four_classification_prefix_00235_1_7
  · exact middle_four_classification_prefix_00235_2_1
  · exact middle_four_classification_prefix_00235_2_2
  · exact middle_four_classification_prefix_00235_2_3
  · exact middle_four_classification_prefix_00235_3_1
  · exact middle_four_classification_prefix_00235_4_1

end AiMathLab.P0054.MiddleSevenNineFinite
