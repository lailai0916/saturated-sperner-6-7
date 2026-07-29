import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector33 : List Nat :=
  [1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0]

theorem middleFourDegreeFourVector33_certificate :
    middleFourMultiplicityCertificate.getD 33 [] =
      middleFourDegreeFourVector33 := by
  decide

def middleFourDegreeFourVector33BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {1, 2, 4}, {0, 3, 5}, {0, 3, 4}]

def middleFourDegreeFourVector33Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {1, 2, 4}, {0, 3, 5}, {0, 3, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector33_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector33 =
      middleFourDegreeFourVector33BlockerRows := by
  decide

theorem middleFourDegreeFourVector33_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector33 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector33_blocker_rows]
  decide

theorem middleFourDegreeFourVector33_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector33 [] =
      middleFourDegreeFourVector33Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector33_blocker_rows]
  decide

theorem middleFourDegreeFourVector33_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector33 [] =
      [middleFourDegreeFourVector33Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector33_base]
  decide

theorem middleFourDegreeFourVector33_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector33 =
      [middleFourDegreeFourVector33Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector33_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector33_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector33_final_card :
    (fastBlocker middleFourDegreeFourVector33Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector33_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector33 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector33_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector33_final_card]
  decide

end AiMathLab.P0054.G420
