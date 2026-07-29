import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector08 : List Nat :=
  [1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0]

theorem middleFourDegreeFourVector08_certificate :
    middleFourMultiplicityCertificate.getD 8 [] =
      middleFourDegreeFourVector08 := by
  decide

def middleFourDegreeFourVector08BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 6}, {1, 5}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

def middleFourDegreeFourVector08Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 7}, {2, 4, 7}, {1, 6, 7}, {1, 5, 7}, {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector08_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector08 =
      middleFourDegreeFourVector08BlockerRows := by
  decide

theorem middleFourDegreeFourVector08_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector08 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector08_blocker_rows]
  decide

theorem middleFourDegreeFourVector08_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector08 [] =
      middleFourDegreeFourVector08Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector08_blocker_rows]
  decide

theorem middleFourDegreeFourVector08_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector08 [] =
      [middleFourDegreeFourVector08Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector08_base]
  decide

theorem middleFourDegreeFourVector08_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector08 =
      [middleFourDegreeFourVector08Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector08_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector08_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector08_final_card :
    (fastBlocker middleFourDegreeFourVector08Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector08_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector08 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector08_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector08_final_card]
  decide

end AiMathLab.P0054.G420
