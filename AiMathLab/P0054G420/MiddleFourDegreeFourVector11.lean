import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector11 : List Nat :=
  [0, 0, 2, 0, 0, 2, 0, 1, 1, 0, 0, 1, 0, 0]

theorem middleFourDegreeFourVector11_certificate :
    middleFourMultiplicityCertificate.getD 11 [] =
      middleFourDegreeFourVector11 := by
  decide

def middleFourDegreeFourVector11BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 4}]

def middleFourDegreeFourVector11Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector11_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector11 =
      middleFourDegreeFourVector11BlockerRows := by
  decide

theorem middleFourDegreeFourVector11_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector11 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector11_blocker_rows]
  decide

theorem middleFourDegreeFourVector11_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector11 [] =
      middleFourDegreeFourVector11Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector11_blocker_rows]
  decide

theorem middleFourDegreeFourVector11_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector11 [] =
      [middleFourDegreeFourVector11Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector11_base]
  decide

theorem middleFourDegreeFourVector11_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector11 =
      [middleFourDegreeFourVector11Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector11_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector11_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector11_final_card :
    (fastBlocker middleFourDegreeFourVector11Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector11_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector11 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector11_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector11_final_card]
  decide

end AiMathLab.P0054.G420
