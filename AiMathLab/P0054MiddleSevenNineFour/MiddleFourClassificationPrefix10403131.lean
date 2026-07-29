import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix104031311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix104031312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix104031313
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix104031314

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_10403_1_3_1 :
    middleFourClassificationValuesCheck 10403 [1, 3, 1] = true := by
  have hSupports : fourMaskSupports 10403 = [0, 1, 5, 7, 11, 13] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    change k ∈ [1, 2, 3, 4] at hk
    simpa using hk
  rcases hkValues with rfl | rfl | rfl | rfl
  · have h := middle_four_classification_prefix_10403_1_3_1_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_10403_1_3_1_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_10403_1_3_1_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_10403_1_3_1_4
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
