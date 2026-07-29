import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00173
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017915
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017916
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017917
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017924
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017925
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017926
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017933
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017934
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017935
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017943
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017944
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017952
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017953
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017961
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017962
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0017971

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00179 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [2, 6], [3, 1], [3, 2], [3, 3], [3, 4], [3, 5], [4, 1], [4, 2], [4, 3], [4, 4], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 179) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00179_1_1
  · exact middle_four_classification_prefix_00179_1_2
  · exact middle_four_classification_prefix_00179_1_3
  · exact middle_four_classification_prefix_00179_1_4
  · exact middle_four_classification_prefix_00179_1_5
  · exact middle_four_classification_prefix_00179_1_6
  · exact middle_four_classification_prefix_00179_1_7
  · exact middle_four_classification_prefix_00179_2_1
  · exact middle_four_classification_prefix_00179_2_2
  · exact middle_four_classification_prefix_00179_2_3
  · exact middle_four_classification_prefix_00179_2_4
  · exact middle_four_classification_prefix_00179_2_5
  · exact middle_four_classification_prefix_00179_2_6
  · exact middle_four_classification_prefix_00179_3_1
  · exact middle_four_classification_prefix_00179_3_2
  · exact middle_four_classification_prefix_00179_3_3
  · exact middle_four_classification_prefix_00179_3_4
  · exact middle_four_classification_prefix_00179_3_5
  · exact middle_four_classification_prefix_00179_4_1
  · exact middle_four_classification_prefix_00179_4_2
  · exact middle_four_classification_prefix_00179_4_3
  · exact middle_four_classification_prefix_00179_4_4
  · exact middle_four_classification_prefix_00179_5_1
  · exact middle_four_classification_prefix_00179_5_2
  · exact middle_four_classification_prefix_00179_5_3
  · exact middle_four_classification_prefix_00179_6_1
  · exact middle_four_classification_prefix_00179_6_2
  · exact middle_four_classification_prefix_00179_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
