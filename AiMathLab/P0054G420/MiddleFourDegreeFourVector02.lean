import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector02 : List Nat :=
  [0, 0, 0, 1, 1, 1, 0, 0, 2, 2, 0, 0, 0, 0]

theorem middleFourDegreeFourVector02_certificate :
    middleFourMultiplicityCertificate.getD 2 [] =
      middleFourDegreeFourVector02 := by
  decide

def middleFourDegreeFourVector02BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4}, {2, 3}, {1, 6}, {1, 5}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

def middleFourDegreeFourVector02Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 7}, {2, 3, 7}, {1, 6, 7}, {1, 5, 7}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector02_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector02 =
      middleFourDegreeFourVector02BlockerRows := by
  decide

theorem middleFourDegreeFourVector02_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector02 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector02_blocker_rows]
  decide

theorem middleFourDegreeFourVector02_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector02 [] =
      middleFourDegreeFourVector02Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector02_blocker_rows]
  decide

theorem middleFourDegreeFourVector02_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector02 [] =
      [middleFourDegreeFourVector02Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector02_base]
  decide

theorem middleFourDegreeFourVector02_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector02 =
      [middleFourDegreeFourVector02Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector02_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector02_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector02_final_card :
    (fastBlocker middleFourDegreeFourVector02Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector02_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector02 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector02_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector02_final_card]
  decide

end AiMathLab.P0054.G420
