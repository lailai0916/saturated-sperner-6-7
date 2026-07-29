import AiMathLab.P0054MiddleSevenNineExtension.Vector023
import AiMathLab.P0054MiddleSevenNineExtension.Selection023
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck021

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector023_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector023 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector023_selections]
  unfold sevenNineExtensionVector023Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector023_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
