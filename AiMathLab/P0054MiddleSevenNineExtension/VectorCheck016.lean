import AiMathLab.P0054MiddleSevenNineExtension.Vector016
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck014

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector016_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector016 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector016_selections]
  unfold sevenNineExtensionVector016Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector016_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
