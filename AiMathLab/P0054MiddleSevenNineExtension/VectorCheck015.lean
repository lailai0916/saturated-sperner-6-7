import AiMathLab.P0054MiddleSevenNineExtension.Vector015
import AiMathLab.P0054MiddleSevenNineExtension.Selection015
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck013

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector015_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector015 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector015_selections]
  unfold sevenNineExtensionVector015Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector015_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
