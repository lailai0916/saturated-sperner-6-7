import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector18 : List Nat :=
  [1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0]

theorem middleFourDegreeFourVector18_certificate :
    middleFourMultiplicityCertificate.getD 18 [] =
      middleFourDegreeFourVector18 := by
  decide

def middleFourDegreeFourVector18BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 2, 5}]

def middleFourDegreeFourVector18Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector18_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector18 =
      middleFourDegreeFourVector18BlockerRows := by
  decide

theorem middleFourDegreeFourVector18_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector18 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector18_blocker_rows]
  decide

theorem middleFourDegreeFourVector18_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector18 [] =
      middleFourDegreeFourVector18Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector18_blocker_rows]
  decide

theorem middleFourDegreeFourVector18_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector18 [] =
      [middleFourDegreeFourVector18Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector18_base]
  decide

theorem middleFourDegreeFourVector18_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector18 =
      [middleFourDegreeFourVector18Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector18_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector18_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector18_final_card :
    (fastBlocker middleFourDegreeFourVector18Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector18_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector18 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector18_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector18_final_card]
  decide

end AiMathLab.P0054.G420
