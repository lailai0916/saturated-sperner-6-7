import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00143
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015523
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015532
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015551
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015561
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015571
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015581

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00155 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1], [8, 1]].all (middleFourClassificationValuesCheck 155) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00155_1_1
  · exact middle_four_classification_prefix_00155_1_2
  · exact middle_four_classification_prefix_00155_1_3
  · exact middle_four_classification_prefix_00155_1_4
  · exact middle_four_classification_prefix_00155_2_1
  · exact middle_four_classification_prefix_00155_2_2
  · exact middle_four_classification_prefix_00155_2_3
  · exact middle_four_classification_prefix_00155_3_1
  · exact middle_four_classification_prefix_00155_3_2
  · exact middle_four_classification_prefix_00155_4_1
  · exact middle_four_classification_prefix_00155_5_1
  · exact middle_four_classification_prefix_00155_6_1
  · exact middle_four_classification_prefix_00155_7_1
  · exact middle_four_classification_prefix_00155_8_1

end AiMathLab.P0054.MiddleSevenNineFinite
