import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077915
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077916
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077917
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077924
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077925
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077926
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077933
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077934
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077935
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077943
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077944
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077952
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077953
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077961
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077962
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0077971

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00779 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [2, 6], [3, 1], [3, 2], [3, 3], [3, 4], [3, 5], [4, 1], [4, 2], [4, 3], [4, 4], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 779) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00779_1_1
  · exact middle_four_classification_prefix_00779_1_2
  · exact middle_four_classification_prefix_00779_1_3
  · exact middle_four_classification_prefix_00779_1_4
  · exact middle_four_classification_prefix_00779_1_5
  · exact middle_four_classification_prefix_00779_1_6
  · exact middle_four_classification_prefix_00779_1_7
  · exact middle_four_classification_prefix_00779_2_1
  · exact middle_four_classification_prefix_00779_2_2
  · exact middle_four_classification_prefix_00779_2_3
  · exact middle_four_classification_prefix_00779_2_4
  · exact middle_four_classification_prefix_00779_2_5
  · exact middle_four_classification_prefix_00779_2_6
  · exact middle_four_classification_prefix_00779_3_1
  · exact middle_four_classification_prefix_00779_3_2
  · exact middle_four_classification_prefix_00779_3_3
  · exact middle_four_classification_prefix_00779_3_4
  · exact middle_four_classification_prefix_00779_3_5
  · exact middle_four_classification_prefix_00779_4_1
  · exact middle_four_classification_prefix_00779_4_2
  · exact middle_four_classification_prefix_00779_4_3
  · exact middle_four_classification_prefix_00779_4_4
  · exact middle_four_classification_prefix_00779_5_1
  · exact middle_four_classification_prefix_00779_5_2
  · exact middle_four_classification_prefix_00779_5_3
  · exact middle_four_classification_prefix_00779_6_1
  · exact middle_four_classification_prefix_00779_6_2
  · exact middle_four_classification_prefix_00779_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
