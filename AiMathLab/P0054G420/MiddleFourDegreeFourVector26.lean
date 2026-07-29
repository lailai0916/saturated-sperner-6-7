import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector26 : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0]

theorem middleFourDegreeFourVector26_certificate :
    middleFourMultiplicityCertificate.getD 26 [] =
      middleFourDegreeFourVector26 := by
  decide

def middleFourDegreeFourVector26BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 4}, {1, 4}, {1, 2, 5}, {1, 2, 3}, {0, 5}, {0, 2, 3}, {0, 1, 3}]

def middleFourDegreeFourVector26Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 4, 6}, {1, 4, 6}, {1, 2, 5}, {1, 2, 3}, {0, 5, 6}, {0, 2, 3}, {0, 1, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector26_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector26 =
      middleFourDegreeFourVector26BlockerRows := by
  decide

theorem middleFourDegreeFourVector26_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector26 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector26_blocker_rows]
  decide

theorem middleFourDegreeFourVector26_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector26 [] =
      middleFourDegreeFourVector26Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector26_blocker_rows]
  decide

theorem middleFourDegreeFourVector26_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector26 [] =
      [middleFourDegreeFourVector26Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector26_base]
  decide

theorem middleFourDegreeFourVector26_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector26 =
      [middleFourDegreeFourVector26Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector26_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector26_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector26_final_card :
    (fastBlocker middleFourDegreeFourVector26Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector26_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector26 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector26_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector26_final_card]
  decide

end AiMathLab.P0054.G420
