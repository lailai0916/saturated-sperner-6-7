import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02247
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234211
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234212
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234213
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234221
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234222
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234223
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234231
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234232
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234233
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234241
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234242
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234243
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234251
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234252
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234253
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234261
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234262
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0234271

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_02342 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 2342) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_02342_1_1
  · exact middle_four_classification_prefix_02342_1_2
  · exact middle_four_classification_prefix_02342_1_3
  · exact middle_four_classification_prefix_02342_2_1
  · exact middle_four_classification_prefix_02342_2_2
  · exact middle_four_classification_prefix_02342_2_3
  · exact middle_four_classification_prefix_02342_3_1
  · exact middle_four_classification_prefix_02342_3_2
  · exact middle_four_classification_prefix_02342_3_3
  · exact middle_four_classification_prefix_02342_4_1
  · exact middle_four_classification_prefix_02342_4_2
  · exact middle_four_classification_prefix_02342_4_3
  · exact middle_four_classification_prefix_02342_5_1
  · exact middle_four_classification_prefix_02342_5_2
  · exact middle_four_classification_prefix_02342_5_3
  · exact middle_four_classification_prefix_02342_6_1
  · exact middle_four_classification_prefix_02342_6_2
  · exact middle_four_classification_prefix_02342_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
