import AiMathLab.P0054MiddleSevenNineExtension.Vector026
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck024

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector026_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector026 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector026_selections]
  unfold sevenNineExtensionVector026Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector026_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
