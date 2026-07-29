import AiMathLab.P0054MiddleSevenNineExtension.Vector111
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck109

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector111_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector111 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector111_selections]
  unfold sevenNineExtensionVector111Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector111_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
