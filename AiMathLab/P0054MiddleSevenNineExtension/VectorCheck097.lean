import AiMathLab.P0054MiddleSevenNineExtension.Vector097
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck095

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector097_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector097 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector097_selections]
  unfold sevenNineExtensionVector097Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector097_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
