import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector27 : List Nat :=
  [1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0]

theorem middleFourDegreeFourVector27_certificate :
    middleFourMultiplicityCertificate.getD 27 [] =
      middleFourDegreeFourVector27 := by
  decide

def middleFourDegreeFourVector27BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 4, 6}, {1, 2, 4}, {0, 3, 6}, {0, 1, 6}]

def middleFourDegreeFourVector27Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 4, 6}, {1, 2, 4}, {0, 3, 6}, {0, 1, 6}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector27_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector27 =
      middleFourDegreeFourVector27BlockerRows := by
  decide

theorem middleFourDegreeFourVector27_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector27 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector27_blocker_rows]
  decide

theorem middleFourDegreeFourVector27_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector27 [] =
      middleFourDegreeFourVector27Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector27_blocker_rows]
  decide

theorem middleFourDegreeFourVector27_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector27 [] =
      [middleFourDegreeFourVector27Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector27_base]
  decide

theorem middleFourDegreeFourVector27_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector27 =
      [middleFourDegreeFourVector27Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector27_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector27_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector27_final_card :
    (fastBlocker middleFourDegreeFourVector27Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector27_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector27 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector27_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector27_final_card]
  decide

end AiMathLab.P0054.G420
