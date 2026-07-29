import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector31 : List Nat :=
  [0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0]

theorem middleFourDegreeFourVector31_certificate :
    middleFourMultiplicityCertificate.getD 31 [] =
      middleFourDegreeFourVector31 := by
  decide

def middleFourDegreeFourVector31BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}]

def middleFourDegreeFourVector31Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector31_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector31 =
      middleFourDegreeFourVector31BlockerRows := by
  decide

theorem middleFourDegreeFourVector31_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector31 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector31_blocker_rows]
  decide

theorem middleFourDegreeFourVector31_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector31 [] =
      middleFourDegreeFourVector31Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector31_blocker_rows]
  decide

theorem middleFourDegreeFourVector31_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector31 [] =
      [middleFourDegreeFourVector31Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector31_base]
  decide

theorem middleFourDegreeFourVector31_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector31 =
      [middleFourDegreeFourVector31Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector31_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector31_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector31_final_card :
    (fastBlocker middleFourDegreeFourVector31Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector31_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector31 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector31_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector31_final_card]
  decide

end AiMathLab.P0054.G420
