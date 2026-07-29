import AiMathLab.P0054MiddleSevenNineExtension.Vector119
import AiMathLab.P0054MiddleSevenNineExtension.Selection119
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck117

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector119_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector119 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector119_selections]
  unfold sevenNineExtensionVector119Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector119_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
