import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector14 : List Nat :=
  [1, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0, 2, 0, 0]

theorem middleFourDegreeFourVector14_certificate :
    middleFourMultiplicityCertificate.getD 14 [] =
      middleFourDegreeFourVector14 := by
  decide

def middleFourDegreeFourVector14BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4}, {2, 3}, {1, 6}, {1, 5}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

def middleFourDegreeFourVector14Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 4, 7}, {2, 3, 7}, {1, 6, 7}, {1, 5, 7}, {0, 4, 6}, {0, 4, 5}, {0, 3, 6}, {0, 3, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector14_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector14 =
      middleFourDegreeFourVector14BlockerRows := by
  decide

theorem middleFourDegreeFourVector14_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector14 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector14_blocker_rows]
  decide

theorem middleFourDegreeFourVector14_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector14 [] =
      middleFourDegreeFourVector14Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector14_blocker_rows]
  decide

theorem middleFourDegreeFourVector14_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector14 [] =
      [middleFourDegreeFourVector14Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector14_base]
  decide

theorem middleFourDegreeFourVector14_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector14 =
      [middleFourDegreeFourVector14Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector14_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector14_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector14_final_card :
    (fastBlocker middleFourDegreeFourVector14Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector14_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector14 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector14_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector14_final_card]
  decide

end AiMathLab.P0054.G420
