import AiMathLab.P0054MiddleSevenNineExtension.Vector094
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck092

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector094_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector094 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector094_selections]
  unfold sevenNineExtensionVector094Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector094_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
