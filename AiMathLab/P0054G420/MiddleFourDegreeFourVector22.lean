import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector22 : List Nat :=
  [0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0]

theorem middleFourDegreeFourVector22_certificate :
    middleFourMultiplicityCertificate.getD 22 [] =
      middleFourDegreeFourVector22 := by
  decide

def middleFourDegreeFourVector22BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5}, {2, 4}, {2, 3}, {1, 4}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3}]

def middleFourDegreeFourVector22Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5, 6}, {2, 4, 6}, {2, 3, 6}, {1, 4, 6}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector22_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector22 =
      middleFourDegreeFourVector22BlockerRows := by
  decide

theorem middleFourDegreeFourVector22_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector22 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector22_blocker_rows]
  decide

theorem middleFourDegreeFourVector22_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector22 [] =
      middleFourDegreeFourVector22Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector22_blocker_rows]
  decide

theorem middleFourDegreeFourVector22_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector22 [] =
      [middleFourDegreeFourVector22Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector22_base]
  decide

theorem middleFourDegreeFourVector22_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector22 =
      [middleFourDegreeFourVector22Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector22_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector22_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector22_final_card :
    (fastBlocker middleFourDegreeFourVector22Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector22_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector22 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector22_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector22_final_card]
  decide

end AiMathLab.P0054.G420
