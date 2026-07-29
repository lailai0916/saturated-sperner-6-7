import AiMathLab.P0054MiddleSevenNineExtension.Vector106
import AiMathLab.P0054MiddleSevenNineExtension.Selection106
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck104

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector106_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector106 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector106_selections]
  unfold sevenNineExtensionVector106Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector106_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
