import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector09 : List Nat :=
  [0, 1, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0]

theorem middleFourDegreeFourVector09_certificate :
    middleFourMultiplicityCertificate.getD 9 [] =
      middleFourDegreeFourVector09 := by
  decide

def middleFourDegreeFourVector09BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4}, {2, 3}, {1, 6}, {1, 5}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

def middleFourDegreeFourVector09Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 7}, {2, 3, 7}, {1, 6, 7}, {1, 5, 7}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector09_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector09 =
      middleFourDegreeFourVector09BlockerRows := by
  decide

theorem middleFourDegreeFourVector09_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector09 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector09_blocker_rows]
  decide

theorem middleFourDegreeFourVector09_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector09 [] =
      middleFourDegreeFourVector09Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector09_blocker_rows]
  decide

theorem middleFourDegreeFourVector09_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector09 [] =
      [middleFourDegreeFourVector09Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector09_base]
  decide

theorem middleFourDegreeFourVector09_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector09 =
      [middleFourDegreeFourVector09Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector09_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector09_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector09_final_card :
    (fastBlocker middleFourDegreeFourVector09Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector09_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector09 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector09_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector09_final_card]
  decide

end AiMathLab.P0054.G420
