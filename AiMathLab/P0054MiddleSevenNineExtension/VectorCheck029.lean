import AiMathLab.P0054MiddleSevenNineExtension.Vector029
import AiMathLab.P0054MiddleSevenNineExtension.Selection029
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck027

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector029_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector029 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector029_selections]
  unfold sevenNineExtensionVector029Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector029_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
