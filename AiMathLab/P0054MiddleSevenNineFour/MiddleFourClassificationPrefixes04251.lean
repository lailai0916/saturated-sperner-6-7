import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes04235
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425141
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425151
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425161
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0425171

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_04251 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 4251) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_04251_1_1
  · exact middle_four_classification_prefix_04251_1_2
  · exact middle_four_classification_prefix_04251_1_3
  · exact middle_four_classification_prefix_04251_2_1
  · exact middle_four_classification_prefix_04251_2_2
  · exact middle_four_classification_prefix_04251_3_1
  · exact middle_four_classification_prefix_04251_4_1
  · exact middle_four_classification_prefix_04251_5_1
  · exact middle_four_classification_prefix_04251_6_1
  · exact middle_four_classification_prefix_04251_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
