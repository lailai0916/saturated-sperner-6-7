import AiMathLab.P0054MiddleSevenNineExtension.Vector113
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck111

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector113_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector113 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector113_selections]
  unfold sevenNineExtensionVector113Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector113_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
