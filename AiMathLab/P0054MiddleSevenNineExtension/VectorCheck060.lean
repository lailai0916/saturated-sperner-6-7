import AiMathLab.P0054MiddleSevenNineExtension.Vector060
import AiMathLab.P0054MiddleSevenNineExtension.Selection060
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck058

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector060_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector060 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector060_selections]
  unfold sevenNineExtensionVector060Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector060_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
