import AiMathLab.P0054G420.FiveRowPairExactFinite

namespace AiMathLab.P0054.G420

def fourExceptionalModelBlockerRows04 :
    List (G413.Row MiddleFourModelPoint) :=
  [{2, 3}, {1, 5}, {1, 4}, {0, 2, 5}, {0, 2, 4}]

set_option maxHeartbeats 10000000 in
-- The explicit blocker-list reduction traverses the finite active-point powerset.
set_option maxRecDepth 1000000 in
theorem four_exceptional_model_blocker_rows_04 :
    middleFourModelBlockerRows
        [0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0] =
      fourExceptionalModelBlockerRows04 := by
  decide

theorem four_exceptional_model_property_04 :
    FourExceptionalModelProperty
      [0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0] := by
  unfold FourExceptionalModelProperty middleFourModelBlocker
  rw [four_exceptional_model_blocker_rows_04]
  constructor
  · decide
  · intro P hP Q hQ hPCard hQCard hne
    simp [fourExceptionalModelBlockerRows04] at hP hQ
    rcases hP with rfl | rfl | rfl | rfl | rfl <;>
      rcases hQ with rfl | rfl | rfl | rfl | rfl <;>
        simp_all

end AiMathLab.P0054.G420

