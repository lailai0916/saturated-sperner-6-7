import AiMathLab.P0054MiddleSevenNineExtension.Vector134
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck132

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector134_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector134 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector134_selections]
  unfold sevenNineExtensionVector134Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector134_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
