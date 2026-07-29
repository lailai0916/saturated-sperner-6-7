import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix014222115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix014491111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix014491112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix014491113
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix014491114
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix014491115
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix014491116

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_01449_1_1_1 :
    middleFourClassificationValuesCheck 1449 [1, 1, 1] = true := by
  have hSupports : fourMaskSupports 1449 = [0, 3, 5, 7, 8, 10] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
    change k ∈ [1, 2, 3, 4, 5, 6] at hk
    simpa using hk
  rcases hkValues with rfl | rfl | rfl | rfl | rfl | rfl
  · have h := middle_four_classification_prefix_01449_1_1_1_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01449_1_1_1_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01449_1_1_1_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01449_1_1_1_4
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01449_1_1_1_5
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01449_1_1_1_6
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
