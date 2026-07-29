import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix1076321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015814
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015823
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015831
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015832
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015833
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015841
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015842
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015851
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015852
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015861
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0015871

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00158 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1], [5, 2], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 158) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00158_1_1
  · exact middle_four_classification_prefix_00158_1_2
  · exact middle_four_classification_prefix_00158_1_3
  · exact middle_four_classification_prefix_00158_1_4
  · exact middle_four_classification_prefix_00158_2_1
  · exact middle_four_classification_prefix_00158_2_2
  · exact middle_four_classification_prefix_00158_2_3
  · exact middle_four_classification_prefix_00158_3_1
  · exact middle_four_classification_prefix_00158_3_2
  · exact middle_four_classification_prefix_00158_3_3
  · exact middle_four_classification_prefix_00158_4_1
  · exact middle_four_classification_prefix_00158_4_2
  · exact middle_four_classification_prefix_00158_5_1
  · exact middle_four_classification_prefix_00158_5_2
  · exact middle_four_classification_prefix_00158_6_1
  · exact middle_four_classification_prefix_00158_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
