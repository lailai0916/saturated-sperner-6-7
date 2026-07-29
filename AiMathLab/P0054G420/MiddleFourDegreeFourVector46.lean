import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector46 : List Nat :=
  [1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1]

theorem middleFourDegreeFourVector46_certificate :
    middleFourMultiplicityCertificate.getD 46 [] =
      middleFourDegreeFourVector46 := by
  decide

def middleFourDegreeFourVector46BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 3, 5}, {1, 3, 4}, {0, 6}, {0, 1, 5}]

def middleFourDegreeFourVector46Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 3, 5}, {1, 3, 4}, {0, 6, 7}, {0, 1, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector46_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector46 =
      middleFourDegreeFourVector46BlockerRows := by
  decide

theorem middleFourDegreeFourVector46_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector46 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector46_blocker_rows]
  decide

theorem middleFourDegreeFourVector46_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector46 [] =
      middleFourDegreeFourVector46Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector46_blocker_rows]
  decide

theorem middleFourDegreeFourVector46_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector46 [] =
      [middleFourDegreeFourVector46Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector46_base]
  decide

theorem middleFourDegreeFourVector46_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector46 =
      [middleFourDegreeFourVector46Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector46_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector46_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector46_final_card :
    (fastBlocker middleFourDegreeFourVector46Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector46_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector46 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector46_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector46_final_card]
  decide

end AiMathLab.P0054.G420
