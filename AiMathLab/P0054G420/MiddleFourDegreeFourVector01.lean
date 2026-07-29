import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourVector01 : List Nat :=
  [0, 1, 0, 0, 2, 1, 0, 0, 2, 1, 0, 0, 0, 0]

theorem middleFourDegreeFourVector01_certificate :
    middleFourMultiplicityCertificate.getD 1 [] =
      middleFourDegreeFourVector01 := by
  decide

def middleFourDegreeFourVector01BlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5}, {3, 4}, {2, 6}, {1, 6}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

def middleFourDegreeFourVector01Candidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 5, 7}, {3, 4, 7}, {2, 6, 7}, {1, 6, 7}, {0, 2, 5}, {0, 2, 4}, {0, 1, 5}, {0, 1, 4}]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector01_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourVector01 =
      middleFourDegreeFourVector01BlockerRows := by
  decide

theorem middleFourDegreeFourVector01_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourVector01 = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourVector01_blocker_rows]
  decide

theorem middleFourDegreeFourVector01_base :
    middleFourModelLiftBaseRows middleFourDegreeFourVector01 [] =
      middleFourDegreeFourVector01Candidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourVector01_blocker_rows]
  decide

theorem middleFourDegreeFourVector01_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourVector01 [] =
      [middleFourDegreeFourVector01Candidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourVector01_base]
  decide

theorem middleFourDegreeFourVector01_candidates :
    middleFourModelCandidateRows middleFourDegreeFourVector01 =
      [middleFourDegreeFourVector01Candidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourVector01_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourVector01_candidates_for_selection]
  simp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourVector01_final_card :
    (fastBlocker middleFourDegreeFourVector01Candidate).card =
      7 := by
  decide

theorem middleFourDegreeFourVector01_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourVector01 = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourVector01_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourVector01_final_card]
  decide

end AiMathLab.P0054.G420
