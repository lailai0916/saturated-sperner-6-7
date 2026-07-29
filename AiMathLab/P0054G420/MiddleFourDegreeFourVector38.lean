import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector38 : List Nat :=
  [1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0]

theorem middleFourDegreeFourVector38_certificate :
    middleFourMultiplicityCertificate.getD 38 [] =
      middleFourDegreeFourVector38 := by
  decide

def middleFourDegreeFourVector38BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {2, 6}, {2, 5}, {2, 3, 4}, {1, 6}, {0, 4, 5}, {0, 3, 4}, {0, 1, 5}]

def middleFourDegreeFourVector38Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {2, 6, 7}, {2, 5, 7}, {2, 3, 4}, {1, 6, 7}, {0, 4, 5}, {0, 3, 4}, {0, 1, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector38_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector38 =
      middleFourDegreeFourVector38BlockerRows := by
  decide

theorem middleFourDegreeFourVector38_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector38 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector38_blocker_rows]
  decide

theorem middleFourDegreeFourVector38_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector38 [] =
      middleFourDegreeFourVector38Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector38_blocker_rows]
  decide

theorem middleFourDegreeFourVector38_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector38 [] =
      [middleFourDegreeFourVector38Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector38_base]
  decide

theorem middleFourDegreeFourVector38_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector38 =
      [middleFourDegreeFourVector38Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector38_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector38_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector38_final_card :
    (fastBlocker middleFourDegreeFourVector38Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector38_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector38 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector38_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector38_final_card]
  decide

end AiMathLab.P0054.G420
