import AiMathLab.P0054G420.FiveRowPairExactFinite

namespace AiMathLab.P0054.G420

def threePaddedModelBlockerRows14 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 4, 5}, {0, 2, 5}, {0, 2, 4}, {0, 2, 3}, {0, 1, 4}]

set_option maxHeartbeats 10000000 in
-- The explicit blocker-list reduction traverses the finite active-point powerset.
set_option maxRecDepth 1000000 in
theorem three_padded_model_blocker_rows_14 :
    middleFourModelBlockerRows
        [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0] =
      threePaddedModelBlockerRows14 := by
  decide

theorem three_padded_model_property_14 :
    ThreePaddedModelProperty
      [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0] := by
  unfold ThreePaddedModelProperty middleFourModelBlocker
  rw [three_padded_model_blocker_rows_14]
  constructor
  · decide
  · intro P hP
    simp [threePaddedModelBlockerRows14] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> decide

end AiMathLab.P0054.G420

