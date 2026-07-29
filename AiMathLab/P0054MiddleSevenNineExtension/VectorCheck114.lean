import AiMathLab.P0054MiddleSevenNineExtension.Vector114
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck112

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector114_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector114 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector114_selections]
  unfold sevenNineExtensionVector114Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector114_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
