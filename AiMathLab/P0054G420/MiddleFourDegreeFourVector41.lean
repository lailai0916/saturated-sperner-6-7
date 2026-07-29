import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector41 : List Nat :=
  [1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1]

theorem middleFourDegreeFourVector41_certificate :
    middleFourMultiplicityCertificate.getD 41 [] =
      middleFourDegreeFourVector41 := by
  decide

def middleFourDegreeFourVector41BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 6}, {2, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 3, 4}]

def middleFourDegreeFourVector41Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 6, 7}, {2, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector41_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector41 =
      middleFourDegreeFourVector41BlockerRows := by
  decide

theorem middleFourDegreeFourVector41_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector41 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector41_blocker_rows]
  decide

theorem middleFourDegreeFourVector41_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector41 [] =
      middleFourDegreeFourVector41Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector41_blocker_rows]
  decide

theorem middleFourDegreeFourVector41_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector41 [] =
      [middleFourDegreeFourVector41Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector41_base]
  decide

theorem middleFourDegreeFourVector41_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector41 =
      [middleFourDegreeFourVector41Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector41_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector41_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector41_final_card :
    (fastBlocker middleFourDegreeFourVector41Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector41_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector41 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector41_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector41_final_card]
  decide

end AiMathLab.P0054.G420
