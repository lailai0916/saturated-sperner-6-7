import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector24 : List Nat :=
  [0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0]

theorem middleFourDegreeFourVector24_certificate :
    middleFourMultiplicityCertificate.getD 24 [] =
      middleFourDegreeFourVector24 := by
  decide

def middleFourDegreeFourVector24BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {2, 5}, {1, 6}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}]

def middleFourDegreeFourVector24Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {2, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 4}, {0, 3, 6}, {0, 3, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector24_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector24 =
      middleFourDegreeFourVector24BlockerRows := by
  decide

theorem middleFourDegreeFourVector24_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector24 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector24_blocker_rows]
  decide

theorem middleFourDegreeFourVector24_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector24 [] =
      middleFourDegreeFourVector24Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector24_blocker_rows]
  decide

theorem middleFourDegreeFourVector24_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector24 [] =
      [middleFourDegreeFourVector24Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector24_base]
  decide

theorem middleFourDegreeFourVector24_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector24 =
      [middleFourDegreeFourVector24Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector24_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector24_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector24_final_card :
    (fastBlocker middleFourDegreeFourVector24Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector24_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector24 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector24_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector24_final_card]
  decide

end AiMathLab.P0054.G420
