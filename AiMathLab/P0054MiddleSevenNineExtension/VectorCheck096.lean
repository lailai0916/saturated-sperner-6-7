import AiMathLab.P0054MiddleSevenNineExtension.Vector096
import AiMathLab.P0054MiddleSevenNineExtension.Selection096
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck094

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector096_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector096 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector096_selections]
  unfold sevenNineExtensionVector096Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector096_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
