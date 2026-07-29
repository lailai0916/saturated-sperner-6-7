import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector00 : List Nat :=
  [1, 0, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0]

theorem middleFourDegreeFourVector00_certificate :
    middleFourMultiplicityCertificate.getD 0 [] =
      middleFourDegreeFourVector00 := by
  decide

def middleFourDegreeFourVector00BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 6}, {1, 5}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

def middleFourDegreeFourVector00Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 4, 7}, {1, 6, 7}, {1, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector00_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector00 =
      middleFourDegreeFourVector00BlockerRows := by
  decide

theorem middleFourDegreeFourVector00_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector00 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector00_blocker_rows]
  decide

theorem middleFourDegreeFourVector00_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector00 [] =
      middleFourDegreeFourVector00Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector00_blocker_rows]
  decide

theorem middleFourDegreeFourVector00_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector00 [] =
      [middleFourDegreeFourVector00Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector00_base]
  decide

theorem middleFourDegreeFourVector00_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector00 =
      [middleFourDegreeFourVector00Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector00_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector00_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector00_final_card :
    (fastBlocker middleFourDegreeFourVector00Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector00_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector00 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector00_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector00_final_card]
  decide

end AiMathLab.P0054.G420
