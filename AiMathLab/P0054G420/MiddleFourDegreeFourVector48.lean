import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector48 : List Nat :=
  [0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1]

theorem middleFourDegreeFourVector48_certificate :
    middleFourMultiplicityCertificate.getD 48 [] =
      middleFourDegreeFourVector48 := by
  decide

def middleFourDegreeFourVector48BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 5}, {1, 4}, {1, 2, 3}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}]

def middleFourDegreeFourVector48Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 6}, {2, 5, 6}, {1, 5, 6}, {1, 4, 6}, {1, 2, 3}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector48_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector48 =
      middleFourDegreeFourVector48BlockerRows := by
  decide

theorem middleFourDegreeFourVector48_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector48 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector48_blocker_rows]
  decide

theorem middleFourDegreeFourVector48_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector48 [] =
      middleFourDegreeFourVector48Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector48_blocker_rows]
  decide

theorem middleFourDegreeFourVector48_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector48 [] =
      [middleFourDegreeFourVector48Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector48_base]
  decide

theorem middleFourDegreeFourVector48_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector48 =
      [middleFourDegreeFourVector48Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector48_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector48_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector48_final_card :
    (fastBlocker middleFourDegreeFourVector48Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector48_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector48 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector48_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector48_final_card]
  decide

end AiMathLab.P0054.G420
