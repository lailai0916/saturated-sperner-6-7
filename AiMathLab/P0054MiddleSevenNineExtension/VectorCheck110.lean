import AiMathLab.P0054MiddleSevenNineExtension.Vector110
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck108

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector110_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector110 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector110_selections]
  unfold sevenNineExtensionVector110Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector110_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
