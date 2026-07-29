import AiMathLab.P0054MiddleSevenNineExtension.Vector128
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck126

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector128_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector128 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector128_selections]
  unfold sevenNineExtensionVector128Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector128_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
