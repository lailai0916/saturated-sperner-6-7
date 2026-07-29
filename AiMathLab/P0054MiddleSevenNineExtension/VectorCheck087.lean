import AiMathLab.P0054MiddleSevenNineExtension.Vector087
import AiMathLab.P0054MiddleSevenNineExtension.Selection087
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck085

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector087_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector087 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector087_selections]
  unfold sevenNineExtensionVector087Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector087_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
