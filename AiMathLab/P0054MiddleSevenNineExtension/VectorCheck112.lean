import AiMathLab.P0054MiddleSevenNineExtension.Vector112
import AiMathLab.P0054MiddleSevenNineExtension.Selection112
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck110

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector112_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector112 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector112_selections]
  unfold sevenNineExtensionVector112Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector112_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
