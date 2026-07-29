import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector15 : List Nat :=
  [0, 1, 1, 0, 2, 0, 0, 0, 0, 1, 0, 2, 0, 0]

theorem middleFourDegreeFourVector15_certificate :
    middleFourMultiplicityCertificate.getD 15 [] =
      middleFourDegreeFourVector15 := by
  decide

def middleFourDegreeFourVector15BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 6}, {1, 5}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

def middleFourDegreeFourVector15Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 4, 7}, {1, 6, 7}, {1, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector15_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector15 =
      middleFourDegreeFourVector15BlockerRows := by
  decide

theorem middleFourDegreeFourVector15_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector15 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector15_blocker_rows]
  decide

theorem middleFourDegreeFourVector15_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector15 [] =
      middleFourDegreeFourVector15Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector15_blocker_rows]
  decide

theorem middleFourDegreeFourVector15_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector15 [] =
      [middleFourDegreeFourVector15Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector15_base]
  decide

theorem middleFourDegreeFourVector15_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector15 =
      [middleFourDegreeFourVector15Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector15_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector15_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector15_final_card :
    (fastBlocker middleFourDegreeFourVector15Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector15_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector15 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector15_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector15_final_card]
  decide

end AiMathLab.P0054.G420
