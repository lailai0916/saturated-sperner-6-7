import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix00189311
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix00189312
import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix00189313

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_00189_3_1 :
    middleFourClassificationValuesCheck 189 [3, 1] = true := by
  have hSupports : fourMaskSupports 189 = [0, 2, 3, 4, 5, 7] := by
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
  · have h := middle_four_classification_prefix_00189_3_1_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00189_3_1_2
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h
  · have h := middle_four_classification_prefix_00189_3_1_3
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
