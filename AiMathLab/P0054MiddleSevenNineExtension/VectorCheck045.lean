import AiMathLab.P0054MiddleSevenNineExtension.Vector045
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck043

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector045_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector045 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector045_selections]
  unfold sevenNineExtensionVector045Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector045_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
