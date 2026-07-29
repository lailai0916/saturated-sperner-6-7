import AiMathLab.P0054MiddleSevenNineExtension.Vector121
import AiMathLab.P0054MiddleSevenNineExtension.Selection121
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck119

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector121_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector121 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector121_selections]
  unfold sevenNineExtensionVector121Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector121_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
