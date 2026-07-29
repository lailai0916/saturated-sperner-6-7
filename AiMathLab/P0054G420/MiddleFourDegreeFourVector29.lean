import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector29 : List Nat :=
  [1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0]

theorem middleFourDegreeFourVector29_certificate :
    middleFourMultiplicityCertificate.getD 29 [] =
      middleFourDegreeFourVector29 := by
  decide

def middleFourDegreeFourVector29BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 3, 6}, {0, 4, 6}, {0, 2, 4}, {0, 1, 6}]

def middleFourDegreeFourVector29Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 3, 6}, {0, 4, 6}, {0, 2, 4}, {0, 1, 6}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector29_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector29 =
      middleFourDegreeFourVector29BlockerRows := by
  decide

theorem middleFourDegreeFourVector29_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector29 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector29_blocker_rows]
  decide

theorem middleFourDegreeFourVector29_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector29 [] =
      middleFourDegreeFourVector29Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector29_blocker_rows]
  decide

theorem middleFourDegreeFourVector29_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector29 [] =
      [middleFourDegreeFourVector29Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector29_base]
  decide

theorem middleFourDegreeFourVector29_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector29 =
      [middleFourDegreeFourVector29Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector29_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector29_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector29_final_card :
    (fastBlocker middleFourDegreeFourVector29Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector29_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector29 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector29_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector29_final_card]
  decide

end AiMathLab.P0054.G420
