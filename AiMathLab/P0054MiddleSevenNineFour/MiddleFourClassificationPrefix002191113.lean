import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021911131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021911132
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021911133
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix0021911134

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_00219_1_1_1_3 :
    middleFourClassificationValuesCheck 219 [1, 1, 1, 3] = true := by
  have hSupports : fourMaskSupports 219 = [0, 1, 3, 4, 6, 7] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    change k ∈ [1, 2, 3, 4] at hk
    simpa using hk
  rcases hkValues with rfl | rfl | rfl | rfl
  · have h := middle_four_classification_prefix_00219_1_1_1_3_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00219_1_1_1_3_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00219_1_1_1_3_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00219_1_1_1_3_4
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
