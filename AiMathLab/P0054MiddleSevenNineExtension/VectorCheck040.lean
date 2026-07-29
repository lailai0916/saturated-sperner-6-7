import AiMathLab.P0054MiddleSevenNineExtension.Vector040
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck038

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector040_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector040 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector040_selections]
  unfold sevenNineExtensionVector040Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector040_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
