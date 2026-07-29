import AiMathLab.P0054MiddleSevenNineExtension.Vector093
import AiMathLab.P0054MiddleSevenNineExtension.Selection093
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck091

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector093_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector093 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector093_selections]
  unfold sevenNineExtensionVector093Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector093_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
