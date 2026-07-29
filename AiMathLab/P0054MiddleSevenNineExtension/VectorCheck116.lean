import AiMathLab.P0054MiddleSevenNineExtension.Vector116
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck114

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector116_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector116 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector116_selections]
  unfold sevenNineExtensionVector116Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector116_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
