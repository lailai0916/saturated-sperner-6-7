import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector40 : List Nat :=
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1]

theorem middleFourDegreeFourVector40_certificate :
    middleFourMultiplicityCertificate.getD 40 [] =
      middleFourDegreeFourVector40 := by
  decide

def middleFourDegreeFourVector40BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 3, 4}]

def middleFourDegreeFourVector40Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector40_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector40 =
      middleFourDegreeFourVector40BlockerRows := by
  decide

theorem middleFourDegreeFourVector40_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector40 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector40_blocker_rows]
  decide

theorem middleFourDegreeFourVector40_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector40 [] =
      middleFourDegreeFourVector40Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector40_blocker_rows]
  decide

theorem middleFourDegreeFourVector40_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector40 [] =
      [middleFourDegreeFourVector40Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector40_base]
  decide

theorem middleFourDegreeFourVector40_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector40 =
      [middleFourDegreeFourVector40Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector40_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector40_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector40_final_card :
    (fastBlocker middleFourDegreeFourVector40Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector40_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector40 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector40_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector40_final_card]
  decide

end AiMathLab.P0054.G420
