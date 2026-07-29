import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector32 : List Nat :=
  [0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]

theorem middleFourDegreeFourVector32_certificate :
    middleFourMultiplicityCertificate.getD 32 [] =
      middleFourDegreeFourVector32 := by
  decide

def middleFourDegreeFourVector32BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6}, {3, 5}, {1, 6}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 3, 4}]

def middleFourDegreeFourVector32Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{5, 6, 7}, {3, 5, 7}, {1, 6, 7}, {1, 3, 4}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 3, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector32_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector32 =
      middleFourDegreeFourVector32BlockerRows := by
  decide

theorem middleFourDegreeFourVector32_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector32 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector32_blocker_rows]
  decide

theorem middleFourDegreeFourVector32_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector32 [] =
      middleFourDegreeFourVector32Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector32_blocker_rows]
  decide

theorem middleFourDegreeFourVector32_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector32 [] =
      [middleFourDegreeFourVector32Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector32_base]
  decide

theorem middleFourDegreeFourVector32_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector32 =
      [middleFourDegreeFourVector32Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector32_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector32_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector32_final_card :
    (fastBlocker middleFourDegreeFourVector32Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector32_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector32 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector32_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector32_final_card]
  decide

end AiMathLab.P0054.G420
