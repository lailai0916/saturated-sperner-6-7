import AiMathLab.P0054MiddleSevenNineFour.MiddleFourClassificationPrefix00235131241

namespace AiMathLab.P0054.MiddleSevenNineFinite

open G419 G420

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_00235_1_3_1_2_4 :
    middleFourClassificationValuesCheck 235 [1, 3, 1, 2, 4] = true := by
  have hSupports : fourMaskSupports 235 = [0, 1, 3, 5, 6, 7] := by
    rfl
  unfold middleFourClassificationValuesCheck
  rw [hSupports]
  simp only [middleFourClassificationValuesCheckAux]
  rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  rw [middleFourClassificationAux, List.all_eq_true]
  intro k hk
  have hkValues : k = 1 := by
    change k ∈ [1] at hk
    simpa using hk
  rcases hkValues with rfl
  · have h := middle_four_classification_prefix_00235_1_3_1_2_4_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.MiddleSevenNineFinite
