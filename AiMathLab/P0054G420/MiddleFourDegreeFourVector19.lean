import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector19 : List Nat :=
  [1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0]

theorem middleFourDegreeFourVector19_certificate :
    middleFourMultiplicityCertificate.getD 19 [] =
      middleFourDegreeFourVector19 := by
  decide

def middleFourDegreeFourVector19BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {2, 5}, {1, 2, 6}, {1, 2, 4}, {0, 5, 6}, {0, 1, 6}]

def middleFourDegreeFourVector19Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {2, 5, 7}, {1, 2, 6}, {1, 2, 4}, {0, 5, 6}, {0, 1, 6}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector19_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector19 =
      middleFourDegreeFourVector19BlockerRows := by
  decide

theorem middleFourDegreeFourVector19_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector19 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector19_blocker_rows]
  decide

theorem middleFourDegreeFourVector19_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector19 [] =
      middleFourDegreeFourVector19Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector19_blocker_rows]
  decide

theorem middleFourDegreeFourVector19_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector19 [] =
      [middleFourDegreeFourVector19Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector19_base]
  decide

theorem middleFourDegreeFourVector19_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector19 =
      [middleFourDegreeFourVector19Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector19_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector19_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector19_final_card :
    (fastBlocker middleFourDegreeFourVector19Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector19_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector19 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector19_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector19_final_card]
  decide

end AiMathLab.P0054.G420
