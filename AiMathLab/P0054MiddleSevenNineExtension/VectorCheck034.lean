import AiMathLab.P0054MiddleSevenNineExtension.Vector034
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck032

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector034_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector034 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector034_selections]
  unfold sevenNineExtensionVector034Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector034_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
