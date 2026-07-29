import AiMathLab.P0054MiddleSevenNineExtension.Vector046
import AiMathLab.P0054MiddleSevenNineExtension.Selection046
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck044

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector046_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector046 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector046_selections]
  unfold sevenNineExtensionVector046Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector046_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
