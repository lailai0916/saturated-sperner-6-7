import AiMathLab.P0054G420.MiddleFourDegreeFourFinite

namespace AiMathLab.P0054.G420

def middleFourDegreeFourProbeValues : List Nat :=
  [1, 0, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 0, 0]

def middleFourDegreeFourProbeBlockerRows :
    List (G413.Row MiddleFourModelPoint) :=
  [{3, 4}, {2, 4}, {1, 6}, {1, 5},
    {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

def middleFourDegreeFourProbeCandidate :
    List (G413.Row MiddleFourModelPoint) :=
  [{7, 3, 4}, {7, 2, 4}, {7, 1, 6}, {7, 1, 5},
    {0, 3, 6}, {0, 3, 5}, {0, 2, 6}, {0, 2, 5}]

def middleFourDegreeFourProbeFinalBlocker :
    G413.Hypergraph MiddleFourModelPoint :=
  {{7, 0}, {4, 1, 0}, {7, 3, 2}, {1, 3, 2},
    {7, 6, 5}, {3, 2, 6, 5}, {4, 6, 5}}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourProbe_blocker_rows :
    middleFourModelBlockerRows middleFourDegreeFourProbeValues =
      middleFourDegreeFourProbeBlockerRows := by
  decide

theorem middleFourDegreeFourProbe_selections :
    middleFourModelLiftSelectionRows middleFourDegreeFourProbeValues = [[]] := by
  unfold middleFourModelLiftSelectionRows middleFourModelOtherBlockerRows
    middleFourModelPairBlockerRows
  rw [middleFourDegreeFourProbe_blocker_rows]
  decide

theorem middleFourDegreeFourProbe_base :
    middleFourModelLiftBaseRows middleFourDegreeFourProbeValues [] =
      middleFourDegreeFourProbeCandidate := by
  unfold middleFourModelLiftBaseRows
  rw [middleFourDegreeFourProbe_blocker_rows]
  decide

theorem middleFourDegreeFourProbe_candidates_for_selection :
    middleFourModelCandidateRowsForSelection
        middleFourDegreeFourProbeValues [] =
      [middleFourDegreeFourProbeCandidate] := by
  unfold middleFourModelCandidateRowsForSelection
  rw [middleFourDegreeFourProbe_base]
  decide

theorem middleFourDegreeFourProbe_candidates :
    middleFourModelCandidateRows middleFourDegreeFourProbeValues =
      [middleFourDegreeFourProbeCandidate] := by
  unfold middleFourModelCandidateRows
  rw [middleFourDegreeFourProbe_selections]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [middleFourDegreeFourProbe_candidates_for_selection]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem middleFourDegreeFourProbe_final_blocker :
    fastBlocker middleFourDegreeFourProbeCandidate =
      middleFourDegreeFourProbeFinalBlocker := by
  decide

theorem middleFourDegreeFourProbe_check :
    middleFourDegreeFourValuesCheck middleFourDegreeFourProbeValues = true := by
  unfold middleFourDegreeFourValuesCheck
  rw [middleFourDegreeFourProbe_candidates]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [middleFourDegreeFourProbe_final_blocker]
  decide

end AiMathLab.P0054.G420
