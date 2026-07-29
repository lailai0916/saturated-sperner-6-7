import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix04251311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix04251312

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_04251_3_1 :
    middleFourClassificationValuesCheck 4251 [3, 1] = true := by
  have hSupports : fourMaskSupports 4251 = [0, 1, 3, 4, 7, 12] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 ∨ k = 2 := by
    change k ∈ [1, 2] at hk
    simpa using hk
  rcases hkValues with rfl | rfl
  · have h := middle_four_classification_prefix_04251_3_1_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_04251_3_1_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
