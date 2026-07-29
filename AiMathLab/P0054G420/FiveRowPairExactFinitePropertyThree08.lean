import AiMathLab.P0054G420.FiveRowPairExactFinite

namespace AiMathLab.P0054.G420

def threePaddedModelBlockerRows08 :
    List (G413.Row MiddleFourModelPoint) :=
  [{0, 5, 6}, {0, 4, 5}, {0, 3, 5}, {0, 2, 6}, {0, 1, 6}]

set_option maxHeartbeats 10000000 in
-- The explicit blocker-list reduction traverses the finite active-point powerset.
set_option maxRecDepth 1000000 in
theorem three_padded_model_blocker_rows_08 :
    middleFourModelBlockerRows
        [1, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0] =
      threePaddedModelBlockerRows08 := by
  decide

theorem three_padded_model_property_08 :
    ThreePaddedModelProperty
      [1, 2, 0, 2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0] := by
  unfold ThreePaddedModelProperty middleFourModelBlocker
  rw [three_padded_model_blocker_rows_08]
  constructor
  · decide
  · intro P hP
    simp [threePaddedModelBlockerRows08] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> decide

end AiMathLab.P0054.G420

