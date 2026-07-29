import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector42 : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1]

theorem middleFourDegreeFourVector42_certificate :
    middleFourMultiplicityCertificate.getD 42 [] =
      middleFourDegreeFourVector42 := by
  decide

def middleFourDegreeFourVector42BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 4}, {1, 5}, {1, 2, 3}, {0, 5}, {0, 2, 3}, {0, 1, 4}, {0, 1, 3}]

def middleFourDegreeFourVector42Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 4, 6}, {1, 5, 6}, {1, 2, 3}, {0, 5, 6}, {0, 2, 3}, {0, 1, 4}, {0, 1, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector42_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector42 =
      middleFourDegreeFourVector42BlockerRows := by
  decide

theorem middleFourDegreeFourVector42_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector42 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector42_blocker_rows]
  decide

theorem middleFourDegreeFourVector42_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector42 [] =
      middleFourDegreeFourVector42Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector42_blocker_rows]
  decide

theorem middleFourDegreeFourVector42_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector42 [] =
      [middleFourDegreeFourVector42Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector42_base]
  decide

theorem middleFourDegreeFourVector42_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector42 =
      [middleFourDegreeFourVector42Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector42_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector42_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector42_final_card :
    (fastBlocker middleFourDegreeFourVector42Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector42_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector42 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector42_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector42_final_card]
  decide

end AiMathLab.P0054.G420
