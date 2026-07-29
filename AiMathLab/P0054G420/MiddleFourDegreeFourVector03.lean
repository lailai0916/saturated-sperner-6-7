import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector03 : List Nat :=
  [0, 0, 0, 0, 2, 2, 0, 1, 1, 1, 0, 0, 0, 0]

theorem middleFourDegreeFourVector03_certificate :
    middleFourMultiplicityCertificate.getD 3 [] =
      middleFourDegreeFourVector03 := by
  decide

def middleFourDegreeFourVector03BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 4}]

def middleFourDegreeFourVector03Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector03_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector03 =
      middleFourDegreeFourVector03BlockerRows := by
  decide

theorem middleFourDegreeFourVector03_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector03 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector03_blocker_rows]
  decide

theorem middleFourDegreeFourVector03_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector03 [] =
      middleFourDegreeFourVector03Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector03_blocker_rows]
  decide

theorem middleFourDegreeFourVector03_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector03 [] =
      [middleFourDegreeFourVector03Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector03_base]
  decide

theorem middleFourDegreeFourVector03_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector03 =
      [middleFourDegreeFourVector03Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector03_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector03_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector03_final_card :
    (fastBlocker middleFourDegreeFourVector03Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector03_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector03 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector03_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector03_final_card]
  decide

end AiMathLab.P0054.G420
