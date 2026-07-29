import AiMathLab.P0054MiddleSevenNineExtension.Vector103
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck101

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector103_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector103 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector103_selections]
  unfold sevenNineExtensionVector103Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector103_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
