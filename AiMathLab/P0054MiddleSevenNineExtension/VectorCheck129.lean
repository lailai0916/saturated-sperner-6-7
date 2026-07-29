import AiMathLab.P0054MiddleSevenNineExtension.Vector129
import AiMathLab.P0054MiddleSevenNineExtension.Selection129
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck127

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector129_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector129 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector129_selections]
  unfold sevenNineExtensionVector129Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector129_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
