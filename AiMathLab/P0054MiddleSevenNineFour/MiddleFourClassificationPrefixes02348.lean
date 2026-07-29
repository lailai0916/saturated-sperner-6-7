import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234811
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234812
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234813
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234814
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234815
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234816
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234817
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234821
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234822
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234823
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234831

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02348 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1]].all (middleFourClassificationValuesCheck 2348) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02348_1_1
  · exact middle_four_classification_prefix_02348_1_2
  · exact middle_four_classification_prefix_02348_1_3
  · exact middle_four_classification_prefix_02348_1_4
  · exact middle_four_classification_prefix_02348_1_5
  · exact middle_four_classification_prefix_02348_1_6
  · exact middle_four_classification_prefix_02348_1_7
  · exact middle_four_classification_prefix_02348_2_1
  · exact middle_four_classification_prefix_02348_2_2
  · exact middle_four_classification_prefix_02348_2_3
  · exact middle_four_classification_prefix_02348_3_1

end AiMathLab.P0054.MiddleSevenNineFinite
