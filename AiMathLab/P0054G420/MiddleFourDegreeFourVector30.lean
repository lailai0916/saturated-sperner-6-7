import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector30 : List Nat :=
  [1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0]

theorem middleFourDegreeFourVector30_certificate :
    middleFourMultiplicityCertificate.getD 30 [] =
      middleFourDegreeFourVector30 := by
  decide

def middleFourDegreeFourVector30BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 4}, {1, 4}, {1, 3}, {1, 2, 5}, {0, 3, 5}, {0, 2, 5}, {0, 2, 3}]

def middleFourDegreeFourVector30Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 4, 6}, {1, 4, 6}, {1, 3, 6}, {1, 2, 5}, {0, 3, 5}, {0, 2, 5}, {0, 2, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector30_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector30 =
      middleFourDegreeFourVector30BlockerRows := by
  decide

theorem middleFourDegreeFourVector30_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector30 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector30_blocker_rows]
  decide

theorem middleFourDegreeFourVector30_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector30 [] =
      middleFourDegreeFourVector30Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector30_blocker_rows]
  decide

theorem middleFourDegreeFourVector30_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector30 [] =
      [middleFourDegreeFourVector30Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector30_base]
  decide

theorem middleFourDegreeFourVector30_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector30 =
      [middleFourDegreeFourVector30Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector30_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector30_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector30_final_card :
    (fastBlocker middleFourDegreeFourVector30Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector30_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector30 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector30_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector30_final_card]
  decide

end AiMathLab.P0054.G420
