import AiMathLab.P0054MiddleSevenNineExtension.Vector064
import AiMathLab.P0054MiddleSevenNineExtension.Selection064
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck062

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector064_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector064 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector064_selections]
  unfold sevenNineExtensionVector064Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector064_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
