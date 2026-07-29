import AiMathLab.P0054MiddleSevenNineExtension.Vector073
import AiMathLab.P0054MiddleSevenNineExtension.Selection073
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck071

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector073_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector073 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector073_selections]
  unfold sevenNineExtensionVector073Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector073_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
