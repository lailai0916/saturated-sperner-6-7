import AiMathLab.P0054MiddleSevenNineExtension.Vector044
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck042

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector044_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector044 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector044_selections]
  unfold sevenNineExtensionVector044Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector044_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
