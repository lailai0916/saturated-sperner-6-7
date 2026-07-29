import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefixes02581
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308711
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308712
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308713
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308714
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308715
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308716
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308721
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308722
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308723
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308731
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308732
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308741
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308751
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0308761

namespace AiMathLab.P0054.MiddleSevenNineFinite

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Separate prefix modules keep the exhaustive certificate within memory bounds.
theorem middle_four_classification_prefixes_03087 :
    [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 1], [2, 2], [2, 3], [3, 1], [3, 2], [4, 1], [5, 1], [6, 1]].all (middleFourClassificationValuesCheck 3087) = true := by
  rw [List.all_eq_true]
  intro values hValues
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hValues
  rcases hValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact middle_four_classification_prefix_03087_1_1
  · exact middle_four_classification_prefix_03087_1_2
  · exact middle_four_classification_prefix_03087_1_3
  · exact middle_four_classification_prefix_03087_1_4
  · exact middle_four_classification_prefix_03087_1_5
  · exact middle_four_classification_prefix_03087_1_6
  · exact middle_four_classification_prefix_03087_2_1
  · exact middle_four_classification_prefix_03087_2_2
  · exact middle_four_classification_prefix_03087_2_3
  · exact middle_four_classification_prefix_03087_3_1
  · exact middle_four_classification_prefix_03087_3_2
  · exact middle_four_classification_prefix_03087_4_1
  · exact middle_four_classification_prefix_03087_5_1
  · exact middle_four_classification_prefix_03087_6_1

end AiMathLab.P0054.MiddleSevenNineFinite
