import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01803
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423511
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423512
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423513
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423514
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423521
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423522
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423523
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423531
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423532
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423541
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423551
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423561
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423571
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0423581

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04235 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1], [8, 1]].all (middleFourClassificationValuesCheck 4235) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04235_1_1
  · exact middle_four_classification_prefix_04235_1_2
  · exact middle_four_classification_prefix_04235_1_3
  · exact middle_four_classification_prefix_04235_1_4
  · exact middle_four_classification_prefix_04235_2_1
  · exact middle_four_classification_prefix_04235_2_2
  · exact middle_four_classification_prefix_04235_2_3
  · exact middle_four_classification_prefix_04235_3_1
  · exact middle_four_classification_prefix_04235_3_2
  · exact middle_four_classification_prefix_04235_4_1
  · exact middle_four_classification_prefix_04235_5_1
  · exact middle_four_classification_prefix_04235_6_1
  · exact middle_four_classification_prefix_04235_7_1
  · exact middle_four_classification_prefix_04235_8_1

end AiMathLab.P0054.MiddleSevenNineFinite
