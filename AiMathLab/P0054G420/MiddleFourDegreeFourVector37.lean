import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector37 : List Nat :=
  [1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0]

theorem middleFourDegreeFourVector37_certificate :
    middleFourMultiplicityCertificate.getD 37 [] =
      middleFourDegreeFourVector37 := by
  decide

def middleFourDegreeFourVector37BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {0, 3, 5}, {0, 3, 4}, {0, 1, 5}]

def middleFourDegreeFourVector37Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {0, 3, 5}, {0, 3, 4}, {0, 1, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector37_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector37 =
      middleFourDegreeFourVector37BlockerRows := by
  decide

theorem middleFourDegreeFourVector37_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector37 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector37_blocker_rows]
  decide

theorem middleFourDegreeFourVector37_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector37 [] =
      middleFourDegreeFourVector37Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector37_blocker_rows]
  decide

theorem middleFourDegreeFourVector37_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector37 [] =
      [middleFourDegreeFourVector37Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector37_base]
  decide

theorem middleFourDegreeFourVector37_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector37 =
      [middleFourDegreeFourVector37Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector37_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector37_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector37_final_card :
    (fastBlocker middleFourDegreeFourVector37Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector37_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector37 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector37_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector37_final_card]
  decide

end AiMathLab.P0054.G420
