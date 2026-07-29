import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector45 : List Nat :=
  [0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1]

theorem middleFourDegreeFourVector45_certificate :
    middleFourMultiplicityCertificate.getD 45 [] =
      middleFourDegreeFourVector45 := by
  decide

def middleFourDegreeFourVector45BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {2, 4}, {1, 3, 4}, {0, 5}, {0, 2, 3}, {0, 1, 4}, {0, 1, 3}]

def middleFourDegreeFourVector45Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 6}, {2, 5, 6}, {2, 4, 6}, {1, 3, 4}, {0, 5, 6}, {0, 2, 3}, {0, 1, 4}, {0, 1, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector45_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector45 =
      middleFourDegreeFourVector45BlockerRows := by
  decide

theorem middleFourDegreeFourVector45_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector45 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector45_blocker_rows]
  decide

theorem middleFourDegreeFourVector45_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector45 [] =
      middleFourDegreeFourVector45Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector45_blocker_rows]
  decide

theorem middleFourDegreeFourVector45_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector45 [] =
      [middleFourDegreeFourVector45Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector45_base]
  decide

theorem middleFourDegreeFourVector45_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector45 =
      [middleFourDegreeFourVector45Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector45_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector45_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector45_final_card :
    (fastBlocker middleFourDegreeFourVector45Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector45_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector45 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector45_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector45_final_card]
  decide

end AiMathLab.P0054.G420
