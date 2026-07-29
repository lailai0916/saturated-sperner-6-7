import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector06 : List Nat :=
  [0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0]

theorem middleFourDegreeFourVector06_certificate :
    middleFourMultiplicityCertificate.getD 6 [] =
      middleFourDegreeFourVector06 := by
  decide

def middleFourDegreeFourVector06BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {2, 6}, {2, 3, 4}, {1, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}]

def middleFourDegreeFourVector06Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 6, 7}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector06_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector06 =
      middleFourDegreeFourVector06BlockerRows := by
  decide

theorem middleFourDegreeFourVector06_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector06 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector06_blocker_rows]
  decide

theorem middleFourDegreeFourVector06_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector06 [] =
      middleFourDegreeFourVector06Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector06_blocker_rows]
  decide

theorem middleFourDegreeFourVector06_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector06 [] =
      [middleFourDegreeFourVector06Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector06_base]
  decide

theorem middleFourDegreeFourVector06_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector06 =
      [middleFourDegreeFourVector06Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector06_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector06_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector06_final_card :
    (fastBlocker middleFourDegreeFourVector06Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector06_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector06 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector06_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector06_final_card]
  decide

end AiMathLab.P0054.G420
