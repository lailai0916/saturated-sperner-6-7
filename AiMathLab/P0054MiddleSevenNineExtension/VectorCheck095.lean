import AiMathLab.P0054MiddleSevenNineExtension.Vector095
import AiMathLab.P0054MiddleSevenNineExtension.Selection095
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck093

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector095_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector095 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector095_selections]
  unfold sevenNineExtensionVector095Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector095_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
