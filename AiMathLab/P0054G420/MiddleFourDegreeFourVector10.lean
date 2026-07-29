import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector10 : List Nat :=
  [0, 0, 2, 1, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0]

theorem middleFourDegreeFourVector10_certificate :
    middleFourMultiplicityCertificate.getD 10 [] =
      middleFourDegreeFourVector10 := by
  decide

def middleFourDegreeFourVector10BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}, {0, 2, 4}]

def middleFourDegreeFourVector10Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}, {0, 2, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector10_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector10 =
      middleFourDegreeFourVector10BlockerRows := by
  decide

theorem middleFourDegreeFourVector10_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector10 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector10_blocker_rows]
  decide

theorem middleFourDegreeFourVector10_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector10 [] =
      middleFourDegreeFourVector10Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector10_blocker_rows]
  decide

theorem middleFourDegreeFourVector10_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector10 [] =
      [middleFourDegreeFourVector10Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector10_base]
  decide

theorem middleFourDegreeFourVector10_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector10 =
      [middleFourDegreeFourVector10Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector10_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector10_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector10_final_card :
    (fastBlocker middleFourDegreeFourVector10Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector10_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector10 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector10_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector10_final_card]
  decide

end AiMathLab.P0054.G420
