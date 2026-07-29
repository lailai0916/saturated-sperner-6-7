import AiMathLab.P0054MiddleSevenNineExtension.Vector127
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck125

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector127_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector127 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector127_selections]
  unfold sevenNineExtensionVector127Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector127_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
