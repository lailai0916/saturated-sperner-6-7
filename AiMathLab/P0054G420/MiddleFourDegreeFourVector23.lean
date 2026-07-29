import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector23 : List Nat :=
  [1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0]

theorem middleFourDegreeFourVector23_certificate :
    middleFourMultiplicityCertificate.getD 23 [] =
      middleFourDegreeFourVector23 := by
  decide

def middleFourDegreeFourVector23BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5}, {2, 4}, {2, 3}, {1, 3}, {0, 4, 5}, {0, 1, 5}, {0, 1, 4}]

def middleFourDegreeFourVector23Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5, 6}, {2, 4, 6}, {2, 3, 6}, {1, 3, 6}, {0, 4, 5}, {0, 1, 5}, {0, 1, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector23_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector23 =
      middleFourDegreeFourVector23BlockerRows := by
  decide

theorem middleFourDegreeFourVector23_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector23 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector23_blocker_rows]
  decide

theorem middleFourDegreeFourVector23_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector23 [] =
      middleFourDegreeFourVector23Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector23_blocker_rows]
  decide

theorem middleFourDegreeFourVector23_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector23 [] =
      [middleFourDegreeFourVector23Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector23_base]
  decide

theorem middleFourDegreeFourVector23_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector23 =
      [middleFourDegreeFourVector23Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector23_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector23_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector23_final_card :
    (fastBlocker middleFourDegreeFourVector23Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector23_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector23 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector23_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector23_final_card]
  decide

end AiMathLab.P0054.G420
