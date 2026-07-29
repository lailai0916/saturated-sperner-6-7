import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes01178
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119321
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119322
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119323
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119331
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119332
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119333
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119341
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119342
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119343
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119351
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119352
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119353
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119361
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119362
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0119371

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_01193 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [3, 3], [4, 1], [4, 2], [4, 3], [5, 1], [5, 2], [5, 3], [6, 1], [6, 2], [7, 1]].all (middleFourClassificationValuesCheck 1193) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_01193_1_1
  · exact middle_four_classification_prefix_01193_1_2
  · exact middle_four_classification_prefix_01193_1_3
  · exact middle_four_classification_prefix_01193_2_1
  · exact middle_four_classification_prefix_01193_2_2
  · exact middle_four_classification_prefix_01193_2_3
  · exact middle_four_classification_prefix_01193_3_1
  · exact middle_four_classification_prefix_01193_3_2
  · exact middle_four_classification_prefix_01193_3_3
  · exact middle_four_classification_prefix_01193_4_1
  · exact middle_four_classification_prefix_01193_4_2
  · exact middle_four_classification_prefix_01193_4_3
  · exact middle_four_classification_prefix_01193_5_1
  · exact middle_four_classification_prefix_01193_5_2
  · exact middle_four_classification_prefix_01193_5_3
  · exact middle_four_classification_prefix_01193_6_1
  · exact middle_four_classification_prefix_01193_6_2
  · exact middle_four_classification_prefix_01193_7_1

end AiMathLab.P0054.MiddleSevenNineFinite
