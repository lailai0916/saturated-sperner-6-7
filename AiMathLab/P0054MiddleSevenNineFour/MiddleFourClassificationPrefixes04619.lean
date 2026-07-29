import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04506
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461911
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461912
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461913
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461921
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461922
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461923
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461931
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461932
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461933
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461941
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461942
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461943
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461951
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461952
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461953
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461961
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461962
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0461971

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04619 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 4619) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04619_1_1
  · exact middle_four_classification_prefix_04619_1_2
  · exact middle_four_classification_prefix_04619_1_3
  · exact middle_four_classification_prefix_04619_2_1
  · exact middle_four_classification_prefix_04619_2_2
  · exact middle_four_classification_prefix_04619_2_3
  · exact middle_four_classification_prefix_04619_3_1
  · exact middle_four_classification_prefix_04619_3_2
  · exact middle_four_classification_prefix_04619_3_3
  · exact middle_four_classification_prefix_04619_4_1
  · exact middle_four_classification_prefix_04619_4_2
  · exact middle_four_classification_prefix_04619_4_3
  · exact middle_four_classification_prefix_04619_5_1
  · exact middle_four_classification_prefix_04619_5_2
  · exact middle_four_classification_prefix_04619_5_3
  · exact middle_four_classification_prefix_04619_6_1
  · exact middle_four_classification_prefix_04619_6_2
  · exact middle_four_classification_prefix_04619_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
