import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00239
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039814
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039823
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039831
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039832
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039833
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039841
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039842
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039851
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039852
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039861
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0039871

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00398 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1], [5, 2], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 398) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00398_1_1
  · exact middle_four_classification_prefix_00398_1_2
  · exact middle_four_classification_prefix_00398_1_3
  · exact middle_four_classification_prefix_00398_1_4
  · exact middle_four_classification_prefix_00398_2_1
  · exact middle_four_classification_prefix_00398_2_2
  · exact middle_four_classification_prefix_00398_2_3
  · exact middle_four_classification_prefix_00398_3_1
  · exact middle_four_classification_prefix_00398_3_2
  · exact middle_four_classification_prefix_00398_3_3
  · exact middle_four_classification_prefix_00398_4_1
  · exact middle_four_classification_prefix_00398_4_2
  · exact middle_four_classification_prefix_00398_5_1
  · exact middle_four_classification_prefix_00398_5_2
  · exact middle_four_classification_prefix_00398_6_1
  · exact middle_four_classification_prefix_00398_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
