import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix01675131
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix016752111
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix016752112
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix016752113

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_01675_2_1_1 :
    middleFourClassificationValuesCheck 1675 [2, 1, 1] = true := by
  have hSupports : fourMaskSupports 1675 = [0, 1, 3, 7, 9, 10] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 ∨ k = 2 ∨ k = 3 := by
    change k ∈ [1, 2, 3] at hk
    simpa using hk
  rcases hkValues with rfl | rfl | rfl
  · have h := middle_four_classification_prefix_01675_2_1_1_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01675_2_1_1_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_01675_2_1_1_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
