import AiMathLab.P0054MiddleSevenNineExtension.Vector043
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck041

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector043_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector043 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector043_selections]
  unfold sevenNineExtensionVector043Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector043_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
