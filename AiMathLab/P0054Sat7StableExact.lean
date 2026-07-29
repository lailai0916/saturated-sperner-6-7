import AiMathLab.P0054FanoAdjacentClosed
import AiMathLab.P0054SevenFanoBridge

/-!
# The exact stable saturation number for seven-Sperner systems
-/

namespace AiMathLab.P0054.Sat7StableExact

open AiMathLab.SaturatedSperner

theorem sat_seven_eq_fifty_five :
    IsStableSaturationNumber 7 55 :=
  SevenFanoBridge.stable_of_fano_adjacent
    FanoAdjacentClosed.fano_adjacent_impossible

end AiMathLab.P0054.Sat7StableExact
