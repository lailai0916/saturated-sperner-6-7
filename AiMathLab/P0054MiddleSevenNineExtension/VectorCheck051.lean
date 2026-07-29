import AiMathLab.P0054MiddleSevenNineExtension.Vector051
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck049

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector051_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector051 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector051_selections]
  unfold sevenNineExtensionVector051Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector051_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
