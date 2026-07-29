import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes00819
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095211
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095212
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095213
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095221
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095222
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095223
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095231
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095232
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095241
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095242
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095251
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0095261

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00952 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [4, 2], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 952) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00952_1_1
  · exact middle_four_classification_prefix_00952_1_2
  · exact middle_four_classification_prefix_00952_1_3
  · exact middle_four_classification_prefix_00952_2_1
  · exact middle_four_classification_prefix_00952_2_2
  · exact middle_four_classification_prefix_00952_2_3
  · exact middle_four_classification_prefix_00952_3_1
  · exact middle_four_classification_prefix_00952_3_2
  · exact middle_four_classification_prefix_00952_4_1
  · exact middle_four_classification_prefix_00952_4_2
  · exact middle_four_classification_prefix_00952_5_1
  · exact middle_four_classification_prefix_00952_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
