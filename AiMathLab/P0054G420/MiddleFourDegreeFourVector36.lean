import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector36 : List Nat :=
  [0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0]

theorem middleFourDegreeFourVector36_certificate :
    middleFourMultiplicityCertificate.getD 36 [] =
      middleFourDegreeFourVector36 := by
  decide

def middleFourDegreeFourVector36BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 5}, {2, 3}, {1, 3, 4}, {0, 5}, {0, 2, 4}, {0, 1, 4}, {0, 1, 3}]

def middleFourDegreeFourVector36Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 5, 6}, {2, 3, 6}, {1, 3, 4}, {0, 5, 6}, {0, 2, 4}, {0, 1, 4}, {0, 1, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector36_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector36 =
      middleFourDegreeFourVector36BlockerRows := by
  decide

theorem middleFourDegreeFourVector36_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector36 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector36_blocker_rows]
  decide

theorem middleFourDegreeFourVector36_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector36 [] =
      middleFourDegreeFourVector36Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector36_blocker_rows]
  decide

theorem middleFourDegreeFourVector36_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector36 [] =
      [middleFourDegreeFourVector36Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector36_base]
  decide

theorem middleFourDegreeFourVector36_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector36 =
      [middleFourDegreeFourVector36Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector36_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector36_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector36_final_card :
    (fastBlocker middleFourDegreeFourVector36Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector36_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector36 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector36_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector36_final_card]
  decide

end AiMathLab.P0054.G420
