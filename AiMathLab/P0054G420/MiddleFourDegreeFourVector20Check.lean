import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Selection0
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Selection1
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Selection2
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Selection3
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20Selection4

namespace AiMathLab.P0054.G420

theorem middleFourDegreeFourVector20_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector20 = true := by
  have h0 := middleFourDegreeFourVector20_selection0_check
  simp only [middleFourDegreeFourVector20Selected0] at h0
  have h1 := middleFourDegreeFourVector20_selection1_check
  simp only [middleFourDegreeFourVector20Selected1] at h1
  have h2 := middleFourDegreeFourVector20_selection2_check
  simp only [middleFourDegreeFourVector20Selected2] at h2
  have h3 := middleFourDegreeFourVector20_selection3_check
  simp only [middleFourDegreeFourVector20Selected3] at h3
  have h4 := middleFourDegreeFourVector20_selection4_check
  simp only [middleFourDegreeFourVector20Selected4] at h4
  unfold middleFourDegreeFourValuesCheck middleFourModelCandidateRows
  rw [middleFourDegreeFourVector20_selections]
  unfold middleFourDegreeFourVector20Selections
  simp only [List.flatMap_cons, List.flatMap_nil, List.all_append, List.all_nil,
    Bool.and_true]
  rw [h0]
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  decide

end AiMathLab.P0054.G420
