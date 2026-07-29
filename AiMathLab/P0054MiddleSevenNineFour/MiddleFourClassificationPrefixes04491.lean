import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04251
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449141
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449151
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449161
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0449171

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04491 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 4491) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04491_1_1
  · exact middle_four_classification_prefix_04491_1_2
  · exact middle_four_classification_prefix_04491_1_3
  · exact middle_four_classification_prefix_04491_2_1
  · exact middle_four_classification_prefix_04491_2_2
  · exact middle_four_classification_prefix_04491_3_1
  · exact middle_four_classification_prefix_04491_4_1
  · exact middle_four_classification_prefix_04491_5_1
  · exact middle_four_classification_prefix_04491_6_1
  · exact middle_four_classification_prefix_04491_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
