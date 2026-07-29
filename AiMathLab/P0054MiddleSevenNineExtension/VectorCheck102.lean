import AiMathLab.P0054MiddleSevenNineExtension.Vector102
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck100

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector102_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector102 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector102_selections]
  unfold sevenNineExtensionVector102Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector102_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
