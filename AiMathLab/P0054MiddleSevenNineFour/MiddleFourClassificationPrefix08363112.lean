import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix083631121
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix083631122
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix083631123
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix083631124
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix083631125
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix083631126

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_08363_1_1_2 :
    middleFourClassificationValuesCheck 8363 [1, 1, 2] = true := by
  have hSupports : fourMaskSupports 8363 = [0, 1, 3, 5, 7, 13] := by
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
  · have h := middle_four_classification_prefix_08363_1_1_2_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_08363_1_1_2_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_08363_1_1_2_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_08363_1_1_2_4
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_08363_1_1_2_5
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_08363_1_1_2_6
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
