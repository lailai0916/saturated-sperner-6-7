import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00952
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117823
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117831
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117832
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117833
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117841
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117842
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117843
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117851
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117852
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117853
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117861
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117862
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0117871

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01178 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 1178) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01178_1_1
  · exact middle_four_classification_prefix_01178_1_2
  · exact middle_four_classification_prefix_01178_1_3
  · exact middle_four_classification_prefix_01178_2_1
  · exact middle_four_classification_prefix_01178_2_2
  · exact middle_four_classification_prefix_01178_2_3
  · exact middle_four_classification_prefix_01178_3_1
  · exact middle_four_classification_prefix_01178_3_2
  · exact middle_four_classification_prefix_01178_3_3
  · exact middle_four_classification_prefix_01178_4_1
  · exact middle_four_classification_prefix_01178_4_2
  · exact middle_four_classification_prefix_01178_4_3
  · exact middle_four_classification_prefix_01178_5_1
  · exact middle_four_classification_prefix_01178_5_2
  · exact middle_four_classification_prefix_01178_5_3
  · exact middle_four_classification_prefix_01178_6_1
  · exact middle_four_classification_prefix_01178_6_2
  · exact middle_four_classification_prefix_01178_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
