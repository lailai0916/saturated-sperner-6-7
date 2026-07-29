import AiMathLab.P0054MiddleSevenNineExtension.Vector135
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck133

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector135_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector135 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector135_selections]
  unfold sevenNineExtensionVector135Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector135_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
