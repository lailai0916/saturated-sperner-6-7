import AiMathLab.P0054MiddleSevenNineExtension.Vector101
import AiMathLab.P0054MiddleSevenNineExtension.Selection101
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck099

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector101_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector101 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector101_selections]
  unfold sevenNineExtensionVector101Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector101_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
