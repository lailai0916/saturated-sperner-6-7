import AiMathLab.P0054MiddleSevenNineExtension.Vector117
import AiMathLab.P0054MiddleSevenNineExtension.Selection117
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck115

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector117_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector117 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector117_selections]
  unfold sevenNineExtensionVector117Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector117_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
