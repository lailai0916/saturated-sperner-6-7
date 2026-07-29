import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0849124
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013914
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013915
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013916
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013917
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013918
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013919
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013924
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013933
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013961
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013971
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013981
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0013991

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00139 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [1, 8], [1, 9], [2, 1], [2, 2], [2, 3], [2, 4], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [5, 1], [6, 1], [7, 1], [8, 1], [9, 1]].all (middleFourClassificationValuesCheck 139) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00139_1_1
  · exact middle_four_classification_prefix_00139_1_2
  · exact middle_four_classification_prefix_00139_1_3
  · exact middle_four_classification_prefix_00139_1_4
  · exact middle_four_classification_prefix_00139_1_5
  · exact middle_four_classification_prefix_00139_1_6
  · exact middle_four_classification_prefix_00139_1_7
  · exact middle_four_classification_prefix_00139_1_8
  · exact middle_four_classification_prefix_00139_1_9
  · exact middle_four_classification_prefix_00139_2_1
  · exact middle_four_classification_prefix_00139_2_2
  · exact middle_four_classification_prefix_00139_2_3
  · exact middle_four_classification_prefix_00139_2_4
  · exact middle_four_classification_prefix_00139_3_1
  · exact middle_four_classification_prefix_00139_3_2
  · exact middle_four_classification_prefix_00139_3_3
  · exact middle_four_classification_prefix_00139_4_1
  · exact middle_four_classification_prefix_00139_4_2
  · exact middle_four_classification_prefix_00139_5_1
  · exact middle_four_classification_prefix_00139_6_1
  · exact middle_four_classification_prefix_00139_7_1
  · exact middle_four_classification_prefix_00139_8_1
  · exact middle_four_classification_prefix_00139_9_1

end AiMathLab.P0054.MiddleSevenNineFinite
