import AiMathLab.P0054MiddleSevenNineExtension.Vector089
import AiMathLab.P0054MiddleSevenNineExtension.Selection089
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck087

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector089_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector089 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector089_selections]
  unfold sevenNineExtensionVector089Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector089_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
