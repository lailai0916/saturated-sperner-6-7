import AiMathLab.P0054MiddleSevenNineExtension.Vector036
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck034

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector036_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector036 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector036_selections]
  unfold sevenNineExtensionVector036Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector036_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
