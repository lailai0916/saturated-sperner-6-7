import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020311
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020312
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020313
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020314
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020315
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020316
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020317
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020321
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020322
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020323
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020331
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020332
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020341
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020351
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020361
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0020371

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00203 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [1, 7], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1], [7, 1]].all (middleFourClassificationValuesCheck 203) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00203_1_1
  · exact middle_four_classification_prefix_00203_1_2
  · exact middle_four_classification_prefix_00203_1_3
  · exact middle_four_classification_prefix_00203_1_4
  · exact middle_four_classification_prefix_00203_1_5
  · exact middle_four_classification_prefix_00203_1_6
  · exact middle_four_classification_prefix_00203_1_7
  · exact middle_four_classification_prefix_00203_2_1
  · exact middle_four_classification_prefix_00203_2_2
  · exact middle_four_classification_prefix_00203_2_3
  · exact middle_four_classification_prefix_00203_3_1
  · exact middle_four_classification_prefix_00203_3_2
  · exact middle_four_classification_prefix_00203_4_1
  · exact middle_four_classification_prefix_00203_5_1
  · exact middle_four_classification_prefix_00203_6_1
  · exact middle_four_classification_prefix_00203_7_1

end AiMathLab.P0054.G420
