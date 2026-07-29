import AiMathLab.P0054MiddleSevenNineExtension.Vector125
import AiMathLab.P0054MiddleSevenNineExtension.Selection125
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck123

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector125_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector125 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector125_selections]
  unfold sevenNineExtensionVector125Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector125_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
