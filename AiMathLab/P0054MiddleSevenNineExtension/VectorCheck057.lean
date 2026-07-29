import AiMathLab.P0054MiddleSevenNineExtension.Vector057
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck055

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector057_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector057 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector057_selections]
  unfold sevenNineExtensionVector057Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector057_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
