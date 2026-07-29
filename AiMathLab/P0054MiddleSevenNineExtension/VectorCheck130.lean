import AiMathLab.P0054MiddleSevenNineExtension.Vector130
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck128

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector130_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector130 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector130_selections]
  unfold sevenNineExtensionVector130Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector130_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
