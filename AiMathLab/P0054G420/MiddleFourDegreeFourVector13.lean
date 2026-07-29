import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector13 : List Nat :=
  [1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0]

theorem middleFourDegreeFourVector13_certificate :
    middleFourMultiplicityCertificate.getD 13 [] =
      middleFourDegreeFourVector13 := by
  decide

def middleFourDegreeFourVector13BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 5, 6}, {0, 2, 6}, {0, 2, 4}, {0, 1, 6}]

def middleFourDegreeFourVector13Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 5, 6}, {0, 2, 6}, {0, 2, 4}, {0, 1, 6}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector13_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector13 =
      middleFourDegreeFourVector13BlockerRows := by
  decide

theorem middleFourDegreeFourVector13_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector13 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector13_blocker_rows]
  decide

theorem middleFourDegreeFourVector13_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector13 [] =
      middleFourDegreeFourVector13Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector13_blocker_rows]
  decide

theorem middleFourDegreeFourVector13_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector13 [] =
      [middleFourDegreeFourVector13Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector13_base]
  decide

theorem middleFourDegreeFourVector13_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector13 =
      [middleFourDegreeFourVector13Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector13_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector13_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector13_final_card :
    (fastBlocker middleFourDegreeFourVector13Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector13_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector13 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector13_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector13_final_card]
  decide

end AiMathLab.P0054.G420
