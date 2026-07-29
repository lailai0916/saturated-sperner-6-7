import AiMathLab.P0054G420.MiddleFourClassificationPrefix00219113321

namespace AiMathLab.P0054.G420

open G419

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- The next multiplicity splits an oversized residual search tree.
theorem middle_four_classification_prefix_00219_1_1_3_3_2 :
    middleFourClassificationValuesCheck 219 [1, 1, 3, 3, 2] = true := by
  have hSupports : fourMaskSupports 219 = [0, 1, 3, 4, 6, 7] := by
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
  · have h := middle_four_classification_prefix_00219_1_1_3_3_2_1
    unfold middleFourClassificationValuesCheck at h
    rw [hSupports] at h
    simp only [middleFourClassificationValuesCheckAux] at h
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide)] at h
    exact h

end AiMathLab.P0054.G420
