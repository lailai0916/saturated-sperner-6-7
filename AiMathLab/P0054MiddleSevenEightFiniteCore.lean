import AiMathLab.P0054G420.MiddleFourActualEnumerated
import AiMathLab.P0054G420.MiddleFourDegreeFourVector20

/-!
# Finite core for the seven-plus-eight split

The tight four-row profile is the six-edge `K₄` incidence kernel.  This
module records only the small closed checks; the extra-row argument is
handled structurally through the Fano plane.
-/

namespace AiMathLab.P0054.MiddleSevenEightFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G419
open AiMathLab.P0054.G420

def sevenEightZeroBase (values : List Nat) :
    List (G413.Row MiddleFourModelPoint) :=
  middleFourModelLiftBaseRows values []

def sevenEightK4Values : List Nat :=
  [0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0]

def sevenEightKernelCardCheck (values : List Nat) : Bool :=
  decide ((middleFourModelBlocker values).card = 7)

def sevenEightBaseCheck (values : List Nat) : Bool :=
  decide ((fastBlocker (sevenEightZeroBase values)).card ≠ 8)

set_option maxRecDepth 100000 in
theorem sevenEight_certificate_eq_k4 :
    ∀ values ∈ middleFourMultiplicityCertificate,
      fourWeightedCoverCount values.toArray = 7 →
      fourPairCoverCount values.toArray = 3 →
      values = sevenEightK4Values := by
  decide

theorem sevenEight_k4_eq_vector20 :
    sevenEightK4Values = middleFourDegreeFourVector20 := by
  rfl

theorem sevenEight_k4_kernel_card_check :
    sevenEightKernelCardCheck sevenEightK4Values = true := by
  decide

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
theorem sevenEight_k4_base_check :
    sevenEightBaseCheck sevenEightK4Values = true := by
  decide

end AiMathLab.P0054.MiddleSevenEightFinite
