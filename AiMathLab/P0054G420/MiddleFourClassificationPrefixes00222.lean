import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022211
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022212
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022213
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022221
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022222
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022231
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022232
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022241
import AiMathLab.P0054G420.MiddleFourClassificationPrefix0022251

namespace AiMathLab.P0054.G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_00222 :
    [[1, 1], [1, 2], [1, 3], [2, 1], [2, 2], [3, 1], [3, 2], [4, 1], [5, 1]].all (middleFourClassificationValuesCheck 222) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_00222_1_1
  · exact middle_four_classification_prefix_00222_1_2
  · exact middle_four_classification_prefix_00222_1_3
  · exact middle_four_classification_prefix_00222_2_1
  · exact middle_four_classification_prefix_00222_2_2
  · exact middle_four_classification_prefix_00222_3_1
  · exact middle_four_classification_prefix_00222_3_2
  · exact middle_four_classification_prefix_00222_4_1
  · exact middle_four_classification_prefix_00222_5_1

end AiMathLab.P0054.G420
