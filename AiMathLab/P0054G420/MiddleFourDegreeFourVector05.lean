import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector05 : List Nat :=
  [1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0]

theorem middleFourDegreeFourVector05_certificate :
    middleFourMultiplicityCertificate.getD 5 [] =
      middleFourDegreeFourVector05 := by
  decide

def middleFourDegreeFourVector05BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 5, 6}, {0, 2, 6}, {0, 2, 4}, {0, 1, 6}]

def middleFourDegreeFourVector05Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 5, 6}, {0, 2, 6}, {0, 2, 4}, {0, 1, 6}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector05_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector05 =
      middleFourDegreeFourVector05BlockerRows := by
  decide

theorem middleFourDegreeFourVector05_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector05 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector05_blocker_rows]
  decide

theorem middleFourDegreeFourVector05_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector05 [] =
      middleFourDegreeFourVector05Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector05_blocker_rows]
  decide

theorem middleFourDegreeFourVector05_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector05 [] =
      [middleFourDegreeFourVector05Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector05_base]
  decide

theorem middleFourDegreeFourVector05_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector05 =
      [middleFourDegreeFourVector05Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector05_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector05_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector05_final_card :
    (fastBlocker middleFourDegreeFourVector05Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector05_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector05 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector05_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector05_final_card]
  decide

end AiMathLab.P0054.G420
