import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector44 : List Nat :=
  [1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1]

theorem middleFourDegreeFourVector44_certificate :
    middleFourMultiplicityCertificate.getD 44 [] =
      middleFourDegreeFourVector44 := by
  decide

def middleFourDegreeFourVector44BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6}, {3, 6}, {3, 5}, {2, 4, 5}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 2, 5}]

def middleFourDegreeFourVector44Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{4, 6, 7}, {3, 6, 7}, {3, 5, 7}, {2, 4, 5}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector44_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector44 =
      middleFourDegreeFourVector44BlockerRows := by
  decide

theorem middleFourDegreeFourVector44_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector44 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector44_blocker_rows]
  decide

theorem middleFourDegreeFourVector44_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector44 [] =
      middleFourDegreeFourVector44Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector44_blocker_rows]
  decide

theorem middleFourDegreeFourVector44_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector44 [] =
      [middleFourDegreeFourVector44Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector44_base]
  decide

theorem middleFourDegreeFourVector44_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector44 =
      [middleFourDegreeFourVector44Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector44_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector44_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector44_final_card :
    (fastBlocker middleFourDegreeFourVector44Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector44_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector44 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector44_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector44_final_card]
  decide

end AiMathLab.P0054.G420
