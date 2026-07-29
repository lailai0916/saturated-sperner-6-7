import AiMathLab.P0054MiddleSevenNineExtension.Vector080
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck078

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector080_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector080 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector080_selections]
  unfold sevenNineExtensionVector080Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector080_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
