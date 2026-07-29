import AiMathLab.P0054MiddleSevenNineExtension.Vector069
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck067

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector069_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector069 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector069_selections]
  unfold sevenNineExtensionVector069Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector069_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
