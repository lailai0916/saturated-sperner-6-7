import AiMathLab.P0054G420.FiveRowPairExactFinite

namespace AiMathLab.P0054.G420

def threePaddedModelBlockerRows03 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 2, 5}, {0, 2, 4}, {0, 2, 3}, {0, 1, 5}, {0, 1, 4}]

set_option maxHeartbeats 10000000 in
-- The explicit blocker-list reduction traverses the finite active-point powerset.
set_option maxRecDepth 1000000 in
theorem three_padded_model_blocker_rows_03 :
    middleFourModelBlockerRows
        [1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0] =
      threePaddedModelBlockerRows03 := by
  decide

theorem three_padded_model_property_03 :
    ThreePaddedModelProperty
      [1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0] := by
  unfold ThreePaddedModelProperty middleFourModelBlocker
  rw [three_padded_model_blocker_rows_03]
  constructor
  · decide
  · intro P hP
    simp [threePaddedModelBlockerRows03] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> decide

end AiMathLab.P0054.G420

