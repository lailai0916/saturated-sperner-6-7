import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector28 : List Nat :=
  [0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0]

theorem middleFourDegreeFourVector28_certificate :
    middleFourMultiplicityCertificate.getD 28 [] =
      middleFourDegreeFourVector28 := by
  decide

def middleFourDegreeFourVector28BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 4}, {2, 3}, {1, 4}, {1, 2, 5}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3}]

def middleFourDegreeFourVector28Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 4, 6}, {2, 3, 6}, {1, 4, 6}, {1, 2, 5}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector28_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector28 =
      middleFourDegreeFourVector28BlockerRows := by
  decide

theorem middleFourDegreeFourVector28_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector28 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector28_blocker_rows]
  decide

theorem middleFourDegreeFourVector28_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector28 [] =
      middleFourDegreeFourVector28Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector28_blocker_rows]
  decide

theorem middleFourDegreeFourVector28_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector28 [] =
      [middleFourDegreeFourVector28Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector28_base]
  decide

theorem middleFourDegreeFourVector28_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector28 =
      [middleFourDegreeFourVector28Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector28_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector28_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector28_final_card :
    (fastBlocker middleFourDegreeFourVector28Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector28_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector28 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector28_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector28_final_card]
  decide

end AiMathLab.P0054.G420
