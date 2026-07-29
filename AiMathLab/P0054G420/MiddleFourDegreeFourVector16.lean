import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector16 : List Nat :=
  [0, 0, 2, 1, 1, 0, 0, 0, 0, 2, 0, 1, 0, 0]

theorem middleFourDegreeFourVector16_certificate :
    middleFourMultiplicityCertificate.getD 16 [] =
      middleFourDegreeFourVector16 := by
  decide

def middleFourDegreeFourVector16BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {1, 6}, {1, 2, 5}, {1, 2, 4}, {0, 6}, {0, 2, 5}, {0, 2, 4}]

def middleFourDegreeFourVector16Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {1, 6, 7}, {1, 2, 5}, {1, 2, 4}, {0, 6, 7}, {0, 2, 5}, {0, 2, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector16_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector16 =
      middleFourDegreeFourVector16BlockerRows := by
  decide

theorem middleFourDegreeFourVector16_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector16 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector16_blocker_rows]
  decide

theorem middleFourDegreeFourVector16_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector16 [] =
      middleFourDegreeFourVector16Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector16_blocker_rows]
  decide

theorem middleFourDegreeFourVector16_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector16 [] =
      [middleFourDegreeFourVector16Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector16_base]
  decide

theorem middleFourDegreeFourVector16_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector16 =
      [middleFourDegreeFourVector16Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector16_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector16_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector16_final_card :
    (fastBlocker middleFourDegreeFourVector16Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector16_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector16 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector16_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector16_final_card]
  decide

end AiMathLab.P0054.G420
