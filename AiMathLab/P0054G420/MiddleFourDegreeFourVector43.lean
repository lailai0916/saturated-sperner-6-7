import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector43 : List Nat :=
  [1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1]

theorem middleFourDegreeFourVector43_certificate :
    middleFourMultiplicityCertificate.getD 43 [] =
      middleFourDegreeFourVector43 := by
  decide

def middleFourDegreeFourVector43BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}]

def middleFourDegreeFourVector43Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector43_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector43 =
      middleFourDegreeFourVector43BlockerRows := by
  decide

theorem middleFourDegreeFourVector43_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector43 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector43_blocker_rows]
  decide

theorem middleFourDegreeFourVector43_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector43 [] =
      middleFourDegreeFourVector43Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector43_blocker_rows]
  decide

theorem middleFourDegreeFourVector43_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector43 [] =
      [middleFourDegreeFourVector43Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector43_base]
  decide

theorem middleFourDegreeFourVector43_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector43 =
      [middleFourDegreeFourVector43Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector43_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector43_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector43_final_card :
    (fastBlocker middleFourDegreeFourVector43Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector43_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector43 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector43_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector43_final_card]
  decide

end AiMathLab.P0054.G420
