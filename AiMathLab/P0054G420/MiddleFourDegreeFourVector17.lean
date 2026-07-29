import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector17 : List Nat :=
  [0, 0, 2, 0, 2, 0, 0, 1, 0, 1, 0, 1, 0, 0]

theorem middleFourDegreeFourVector17_certificate :
    middleFourMultiplicityCertificate.getD 17 [] =
      middleFourDegreeFourVector17 := by
  decide

def middleFourDegreeFourVector17BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 6}, {0, 3, 4}, {0, 2, 4}]

def middleFourDegreeFourVector17Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}, {0, 2, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector17_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector17 =
      middleFourDegreeFourVector17BlockerRows := by
  decide

theorem middleFourDegreeFourVector17_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector17 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector17_blocker_rows]
  decide

theorem middleFourDegreeFourVector17_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector17 [] =
      middleFourDegreeFourVector17Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector17_blocker_rows]
  decide

theorem middleFourDegreeFourVector17_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector17 [] =
      [middleFourDegreeFourVector17Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector17_base]
  decide

theorem middleFourDegreeFourVector17_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector17 =
      [middleFourDegreeFourVector17Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector17_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector17_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector17_final_card :
    (fastBlocker middleFourDegreeFourVector17Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector17_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector17 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector17_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector17_final_card]
  decide

end AiMathLab.P0054.G420
