import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector04 : List Nat :=
  [0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0]

theorem middleFourDegreeFourVector04_certificate :
    middleFourMultiplicityCertificate.getD 4 [] =
      middleFourDegreeFourVector04 := by
  decide

def middleFourDegreeFourVector04BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 6}, {1, 5, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}]

def middleFourDegreeFourVector04Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 5, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector04_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector04 =
      middleFourDegreeFourVector04BlockerRows := by
  decide

theorem middleFourDegreeFourVector04_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector04 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector04_blocker_rows]
  decide

theorem middleFourDegreeFourVector04_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector04 [] =
      middleFourDegreeFourVector04Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector04_blocker_rows]
  decide

theorem middleFourDegreeFourVector04_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector04 [] =
      [middleFourDegreeFourVector04Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector04_base]
  decide

theorem middleFourDegreeFourVector04_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector04 =
      [middleFourDegreeFourVector04Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector04_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector04_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector04_final_card :
    (fastBlocker middleFourDegreeFourVector04Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector04_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector04 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector04_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector04_final_card]
  decide

end AiMathLab.P0054.G420
