import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector47 : List Nat :=
  [1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1]

theorem middleFourDegreeFourVector47_certificate :
    middleFourMultiplicityCertificate.getD 47 [] =
      middleFourDegreeFourVector47 := by
  decide

def middleFourDegreeFourVector47BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 4, 5}, {1, 3, 4}, {0, 6}, {0, 1, 5}]

def middleFourDegreeFourVector47Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 4, 5}, {1, 3, 4}, {0, 6, 7}, {0, 1, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector47_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector47 =
      middleFourDegreeFourVector47BlockerRows := by
  decide

theorem middleFourDegreeFourVector47_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector47 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector47_blocker_rows]
  decide

theorem middleFourDegreeFourVector47_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector47 [] =
      middleFourDegreeFourVector47Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector47_blocker_rows]
  decide

theorem middleFourDegreeFourVector47_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector47 [] =
      [middleFourDegreeFourVector47Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector47_base]
  decide

theorem middleFourDegreeFourVector47_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector47 =
      [middleFourDegreeFourVector47Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector47_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector47_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector47_final_card :
    (fastBlocker middleFourDegreeFourVector47Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector47_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector47 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector47_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector47_final_card]
  decide

end AiMathLab.P0054.G420
