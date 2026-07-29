import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector12 : List Nat :=
  [0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0]

theorem middleFourDegreeFourVector12_certificate :
    middleFourMultiplicityCertificate.getD 12 [] =
      middleFourDegreeFourVector12 := by
  decide

def middleFourDegreeFourVector12BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6}, {3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 2, 5}]

def middleFourDegreeFourVector12Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 6, 7}, {3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 5, 6}, {0, 2, 5}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector12_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector12 =
      middleFourDegreeFourVector12BlockerRows := by
  decide

theorem middleFourDegreeFourVector12_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector12 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector12_blocker_rows]
  decide

theorem middleFourDegreeFourVector12_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector12 [] =
      middleFourDegreeFourVector12Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector12_blocker_rows]
  decide

theorem middleFourDegreeFourVector12_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector12 [] =
      [middleFourDegreeFourVector12Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector12_base]
  decide

theorem middleFourDegreeFourVector12_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector12 =
      [middleFourDegreeFourVector12Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector12_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector12_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector12_final_card :
    (fastBlocker middleFourDegreeFourVector12Candidate).card =
      10 := by
  decide

theorem middleFourDegreeFourVector12_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector12 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector12_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector12_final_card]
  decide

end AiMathLab.P0054.G420
