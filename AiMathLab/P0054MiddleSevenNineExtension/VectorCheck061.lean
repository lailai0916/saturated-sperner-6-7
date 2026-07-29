import AiMathLab.P0054MiddleSevenNineExtension.Vector061
import AiMathLab.P0054MiddleSevenNineExtension.Selection061
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck059

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector061_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector061 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector061_selections]
  unfold sevenNineExtensionVector061Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector061_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
