import AiMathLab.P0054MiddleSevenNineExtension.Vector079
import AiMathLab.P0054MiddleSevenNineExtension.Selection079
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck077

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector079_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector079 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector079_selections]
  unfold sevenNineExtensionVector079Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector079_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
