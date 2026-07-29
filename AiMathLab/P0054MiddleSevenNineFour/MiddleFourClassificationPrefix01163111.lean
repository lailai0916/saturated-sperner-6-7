import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix011631111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix011631112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix011631113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix011631114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix011631115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix011631116
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix011631117
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix011631118

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_01163_1_1_1 :
    middleFourClassificationValuesCheck 1163 [1, 1, 1] = true := by
  have hSupports : fourMaskSupports 1163 = [0, 1, 3, 7, 10] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by
    change k ∈ [1, 2, 3, 4, 5, 6, 7, 8] at hk
    simpa using hk
  rcases hkValues with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := middle_four_classification_prefix_01163_1_1_1_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01163_1_1_1_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01163_1_1_1_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01163_1_1_1_4
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01163_1_1_1_5
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01163_1_1_1_6
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01163_1_1_1_7
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01163_1_1_1_8
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
