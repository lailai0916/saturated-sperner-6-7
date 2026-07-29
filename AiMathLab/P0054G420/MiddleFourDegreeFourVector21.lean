import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector21 : List Nat :=
  [0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0]

theorem middleFourDegreeFourVector21_certificate :
    middleFourMultiplicityCertificate.getD 21 [] =
      middleFourDegreeFourVector21 := by
  decide

def middleFourDegreeFourVector21BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5}, {2, 4}, {2, 3}, {1, 3, 4}, {0, 5}, {0, 1, 4}, {0, 1, 3}]

def middleFourDegreeFourVector21Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4, 5}, {2, 5, 6}, {2, 4, 6}, {2, 3, 6}, {1, 3, 4}, {0, 5, 6}, {0, 1, 4}, {0, 1, 3}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector21_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector21 =
      middleFourDegreeFourVector21BlockerRows := by
  decide

theorem middleFourDegreeFourVector21_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector21 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector21_blocker_rows]
  decide

theorem middleFourDegreeFourVector21_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector21 [] =
      middleFourDegreeFourVector21Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector21_blocker_rows]
  decide

theorem middleFourDegreeFourVector21_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector21 [] =
      [middleFourDegreeFourVector21Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector21_base]
  decide

theorem middleFourDegreeFourVector21_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector21 =
      [middleFourDegreeFourVector21Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector21_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector21_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector21_final_card :
    (fastBlocker middleFourDegreeFourVector21Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector21_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector21 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector21_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector21_final_card]
  decide

end AiMathLab.P0054.G420
