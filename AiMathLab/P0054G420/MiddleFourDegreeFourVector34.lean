import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector34 : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0]

theorem middleFourDegreeFourVector34_certificate :
    middleFourMultiplicityCertificate.getD 34 [] =
      middleFourDegreeFourVector34 := by
  decide

def middleFourDegreeFourVector34BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5}, {2, 5}, {1, 4}, {1, 2, 3}, {0, 5}, {0, 2, 4}, {0, 2, 3}, {0, 1, 3}]

def middleFourDegreeFourVector34Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 5, 6}, {2, 5, 6}, {1, 4, 6}, {1, 2, 3}, {0, 5, 6}, {0, 2, 4}, {0, 2, 3}, {0, 1, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector34_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector34 =
      middleFourDegreeFourVector34BlockerRows := by
  decide

theorem middleFourDegreeFourVector34_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector34 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector34_blocker_rows]
  decide

theorem middleFourDegreeFourVector34_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector34 [] =
      middleFourDegreeFourVector34Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector34_blocker_rows]
  decide

theorem middleFourDegreeFourVector34_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector34 [] =
      [middleFourDegreeFourVector34Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector34_base]
  decide

theorem middleFourDegreeFourVector34_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector34 =
      [middleFourDegreeFourVector34Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector34_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector34_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector34_final_card :
    (fastBlocker middleFourDegreeFourVector34Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector34_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector34 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector34_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector34_final_card]
  decide

end AiMathLab.P0054.G420
