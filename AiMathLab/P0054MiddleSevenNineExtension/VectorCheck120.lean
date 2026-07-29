import AiMathLab.P0054MiddleSevenNineExtension.Vector120
import AiMathLab.P0054MiddleSevenNineExtension.Selection120
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck118

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector120_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector120 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector120_selections]
  unfold sevenNineExtensionVector120Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector120_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
