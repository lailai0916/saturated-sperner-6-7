import AiMathLab.P0054MiddleSevenNineExtension.Vector109
import AiMathLab.P0054MiddleSevenNineExtension.Selection109
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck107

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector109_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector109 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector109_selections]
  unfold sevenNineExtensionVector109Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector109_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
