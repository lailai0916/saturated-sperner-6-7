import AiMathLab.P0054MiddleSevenNineExtension.Vector037
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck035

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector037_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector037 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector037_selections]
  unfold sevenNineExtensionVector037Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector037_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
