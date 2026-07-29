import AiMathLab.P0054MiddleSevenNineExtension.Vector041
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck039

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector041_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector041 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector041_selections]
  unfold sevenNineExtensionVector041Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector041_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
