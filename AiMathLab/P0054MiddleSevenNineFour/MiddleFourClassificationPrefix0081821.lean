import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix00818211
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix00818212
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix00818213

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_00818_2_1 :
    middleFourClassificationValuesCheck 818 [2, 1] = true := by
  have hSupports : fourMaskSupports 818 = [1, 4, 5, 8, 9] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 ∨ k = 2 ∨ k = 3 := by
    change k ∈ [1, 2, 3] at hk
    simpa using hk
  rcases hkValues with rfl | rfl | rfl
  · have h := middle_four_classification_prefix_00818_2_1_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00818_2_1_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00818_2_1_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
