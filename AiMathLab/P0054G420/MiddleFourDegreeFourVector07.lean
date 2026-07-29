import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector07 : List Nat :=
  [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0]

theorem middleFourDegreeFourVector07_certificate :
    middleFourMultiplicityCertificate.getD 7 [] =
      middleFourDegreeFourVector07 := by
  decide

def middleFourDegreeFourVector07BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {0, 3, 5}, {0, 3, 4}, {0, 1, 5}]

def middleFourDegreeFourVector07Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {0, 3, 5}, {0, 3, 4}, {0, 1, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector07_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector07 =
      middleFourDegreeFourVector07BlockerRows := by
  decide

theorem middleFourDegreeFourVector07_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector07 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector07_blocker_rows]
  decide

theorem middleFourDegreeFourVector07_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector07 [] =
      middleFourDegreeFourVector07Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector07_blocker_rows]
  decide

theorem middleFourDegreeFourVector07_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector07 [] =
      [middleFourDegreeFourVector07Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector07_base]
  decide

theorem middleFourDegreeFourVector07_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector07 =
      [middleFourDegreeFourVector07Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector07_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector07_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector07_final_card :
    (fastBlocker middleFourDegreeFourVector07Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector07_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector07 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector07_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector07_final_card]
  decide

end AiMathLab.P0054.G420
