import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector39 : List Nat :=
  [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0]

theorem middleFourDegreeFourVector39_certificate :
    middleFourMultiplicityCertificate.getD 39 [] =
      middleFourDegreeFourVector39 := by
  decide

def middleFourDegreeFourVector39BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 5}, {1, 4}, {1, 2, 3}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}]

def middleFourDegreeFourVector39Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 6}, {2, 5, 6}, {1, 5, 6}, {1, 4, 6}, {1, 2, 3}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector39_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector39 =
      middleFourDegreeFourVector39BlockerRows := by
  decide

theorem middleFourDegreeFourVector39_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector39 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector39_blocker_rows]
  decide

theorem middleFourDegreeFourVector39_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector39 [] =
      middleFourDegreeFourVector39Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector39_blocker_rows]
  decide

theorem middleFourDegreeFourVector39_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector39 [] =
      [middleFourDegreeFourVector39Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector39_base]
  decide

theorem middleFourDegreeFourVector39_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector39 =
      [middleFourDegreeFourVector39Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector39_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector39_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector39_final_card :
    (fastBlocker middleFourDegreeFourVector39Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector39_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector39 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector39_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector39_final_card]
  decide

end AiMathLab.P0054.G420
