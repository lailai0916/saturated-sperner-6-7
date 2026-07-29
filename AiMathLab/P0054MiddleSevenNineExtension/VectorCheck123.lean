import AiMathLab.P0054MiddleSevenNineExtension.Vector123
import AiMathLab.P0054MiddleSevenNineExtension.Selection123
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck121

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector123_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector123 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector123_selections]
  unfold sevenNineExtensionVector123Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector123_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
