import AiMathLab.P0054MiddleSevenNineExtension.Vector050
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck048

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector050_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector050 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector050_selections]
  unfold sevenNineExtensionVector050Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector050_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
