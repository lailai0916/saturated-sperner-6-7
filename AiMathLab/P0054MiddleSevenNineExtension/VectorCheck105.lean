import AiMathLab.P0054MiddleSevenNineExtension.Vector105
import AiMathLab.P0054MiddleSevenNineExtension.Selection105
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck103

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector105_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector105 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector105_selections]
  unfold sevenNineExtensionVector105Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector105_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
