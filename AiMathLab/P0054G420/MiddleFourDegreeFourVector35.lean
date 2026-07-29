import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector35 : List Nat :=
  [1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0]

theorem middleFourDegreeFourVector35_certificate :
    middleFourMultiplicityCertificate.getD 35 [] =
      middleFourDegreeFourVector35 := by
  decide

def middleFourDegreeFourVector35BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 6}, {3, 4}, {2, 4, 5}, {1, 6}, {1, 2, 4}, {0, 3, 5}, {0, 2, 5}]

def middleFourDegreeFourVector35Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 6, 7}, {3, 4, 7}, {2, 4, 5}, {1, 6, 7}, {1, 2, 4}, {0, 3, 5}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector35_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector35 =
      middleFourDegreeFourVector35BlockerRows := by
  decide

theorem middleFourDegreeFourVector35_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector35 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector35_blocker_rows]
  decide

theorem middleFourDegreeFourVector35_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector35 [] =
      middleFourDegreeFourVector35Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector35_blocker_rows]
  decide

theorem middleFourDegreeFourVector35_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector35 [] =
      [middleFourDegreeFourVector35Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector35_base]
  decide

theorem middleFourDegreeFourVector35_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector35 =
      [middleFourDegreeFourVector35Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector35_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector35_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector35_final_card :
    (fastBlocker middleFourDegreeFourVector35Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector35_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector35 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector35_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector35_final_card]
  decide

end AiMathLab.P0054.G420
