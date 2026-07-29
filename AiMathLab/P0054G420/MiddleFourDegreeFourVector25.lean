import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector25 : List Nat :=
  [1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0]

theorem middleFourDegreeFourVector25_certificate :
    middleFourMultiplicityCertificate.getD 25 [] =
      middleFourDegreeFourVector25 := by
  decide

def middleFourDegreeFourVector25BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}]

def middleFourDegreeFourVector25Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector25_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector25 =
      middleFourDegreeFourVector25BlockerRows := by
  decide

theorem middleFourDegreeFourVector25_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector25 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector25_blocker_rows]
  decide

theorem middleFourDegreeFourVector25_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector25 [] =
      middleFourDegreeFourVector25Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector25_blocker_rows]
  decide

theorem middleFourDegreeFourVector25_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector25 [] =
      [middleFourDegreeFourVector25Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector25_base]
  decide

theorem middleFourDegreeFourVector25_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector25 =
      [middleFourDegreeFourVector25Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector25_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector25_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector25_final_card :
    (fastBlocker middleFourDegreeFourVector25Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector25_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector25 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector25_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector25_final_card]
  decide

end AiMathLab.P0054.G420
