import AiMathLab.P0054MiddleSevenNineExtension.Vector063
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck061

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector063_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector063 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector063_selections]
  unfold sevenNineExtensionVector063Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector063_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
