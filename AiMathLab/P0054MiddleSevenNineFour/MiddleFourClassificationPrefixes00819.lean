import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00779
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081915
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081916
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081924
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081925
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081933
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081934
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081943
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081952
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0081961

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00819 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5], [3, 1], [3, 2], [3, 3], [3, 4], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [6, 1]].all (middleFourClassificationValuesCheck 819) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00819_1_1
  · exact middle_four_classification_prefix_00819_1_2
  · exact middle_four_classification_prefix_00819_1_3
  · exact middle_four_classification_prefix_00819_1_4
  · exact middle_four_classification_prefix_00819_1_5
  · exact middle_four_classification_prefix_00819_1_6
  · exact middle_four_classification_prefix_00819_2_1
  · exact middle_four_classification_prefix_00819_2_2
  · exact middle_four_classification_prefix_00819_2_3
  · exact middle_four_classification_prefix_00819_2_4
  · exact middle_four_classification_prefix_00819_2_5
  · exact middle_four_classification_prefix_00819_3_1
  · exact middle_four_classification_prefix_00819_3_2
  · exact middle_four_classification_prefix_00819_3_3
  · exact middle_four_classification_prefix_00819_3_4
  · exact middle_four_classification_prefix_00819_4_1
  · exact middle_four_classification_prefix_00819_4_2
  · exact middle_four_classification_prefix_00819_4_3
  · exact middle_four_classification_prefix_00819_5_1
  · exact middle_four_classification_prefix_00819_5_2
  · exact middle_four_classification_prefix_00819_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
