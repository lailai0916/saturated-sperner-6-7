import AiMathLab.P0054MiddleSevenNineExtension.Vector062
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck060

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector062_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector062 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector062_selections]
  unfold sevenNineExtensionVector062Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector062_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
