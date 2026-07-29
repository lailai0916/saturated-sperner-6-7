import AiMathLab.P0054MiddleSevenNineExtension.Vector131
import AiMathLab.P0054MiddleSevenNineExtension.Selection131
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck129

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector131_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector131 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector131_selections]
  unfold sevenNineExtensionVector131Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector131_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
