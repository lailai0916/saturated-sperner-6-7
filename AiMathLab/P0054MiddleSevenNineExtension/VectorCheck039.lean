import AiMathLab.P0054MiddleSevenNineExtension.Vector039
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck037

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector039_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector039 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector039_selections]
  unfold sevenNineExtensionVector039Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector039_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
