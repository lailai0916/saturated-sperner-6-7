import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00817
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081831
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081832
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081841
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081851
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081861
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081871

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00818 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 818) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00818_1_1
  · exact middle_four_classification_prefix_00818_1_2
  · exact middle_four_classification_prefix_00818_1_3
  · exact middle_four_classification_prefix_00818_2_1
  · exact middle_four_classification_prefix_00818_2_2
  · exact middle_four_classification_prefix_00818_3_1
  · exact middle_four_classification_prefix_00818_3_2
  · exact middle_four_classification_prefix_00818_4_1
  · exact middle_four_classification_prefix_00818_5_1
  · exact middle_four_classification_prefix_00818_6_1
  · exact middle_four_classification_prefix_00818_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
