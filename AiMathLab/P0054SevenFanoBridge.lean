import AiMathLab.P0054FanoAdjacentBridge
import AiMathLab.P0054MiddleSevenNineClosed
import AiMathLab.P0054Sat7StableBridge
import AiMathLab.P0054SevenMiddleBridge

/-!
# Final seven-Sperner aggregation from the Fano-adjacent principle

The seven-plus-nine split has a concrete proof.  Consequently the only input
left in the exact global lower bound is the local Fano-adjacent exclusion.
This module records both the finite-ground lower theorem and the stable-number
conclusion parametrically in that one principle.
-/

namespace AiMathLab.P0054.SevenFanoBridge

open AiMathLab.SaturatedSperner

set_option maxHeartbeats 2000000 in
-- The final bridge elaborates the complete canonical-layer lower-bound interface.
theorem family_card_lower_of_fano_adjacent
    (hAdjacent : ∀ {alpha : Type} [Fintype alpha] [DecidableEq alpha],
      AiMathLab.P0054.FanoAdjacentBridge.FanoAdjacentImpossiblePrinciple alpha)
    {n : Nat} (F : AiMathLab.SaturatedSperner.Family (Fin n))
    (hsat : IsSaturatedKSperner 7 F)
    (hground : 3 * 2 ^ F.card ≤ n)
    (hexternal : F.card < 2 ^ n) :
    55 ≤ F.card := by
  apply
    AiMathLab.P0054.SevenMiddleBridge.family_card_lower_of_fourteen_and_seven_nine_exclusions
      hsat (by simpa using hground) (by simpa using hexternal)
  · intro hFamilyCard hMiddle
    exact
      AiMathLab.P0054.FanoAdjacentBridge.fourteen_middle_impossible_of_fano_adjacent
        (alpha := Fin n) (hAdjacent (alpha := Fin n)) hsat
          (by simpa using hground) hFamilyCard hMiddle
  · exact AiMathLab.P0054.MiddleSevenNineClosed.sevenNine_impossible

set_option maxHeartbeats 2000000 in
-- The stable wrapper instantiates the preceding finite-ground bridge.
theorem stable_of_fano_adjacent
    (hAdjacent : ∀ {alpha : Type} [Fintype alpha] [DecidableEq alpha],
      AiMathLab.P0054.FanoAdjacentBridge.FanoAdjacentImpossiblePrinciple alpha) :
    IsStableSaturationNumber 7 55 := by
  apply AiMathLab.P0054.Sat7StableBridge.stable_of_canonical_lower
  intro n F hsat hground hexternal
  exact family_card_lower_of_fano_adjacent hAdjacent F hsat
    (by simpa using hground) (by simpa using hexternal)

end AiMathLab.P0054.SevenFanoBridge
