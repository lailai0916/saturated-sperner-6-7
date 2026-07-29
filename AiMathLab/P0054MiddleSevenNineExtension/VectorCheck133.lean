import AiMathLab.P0054MiddleSevenNineExtension.Vector133
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck131

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector133_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector133 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector133_selections]
  unfold sevenNineExtensionVector133Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector133_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
