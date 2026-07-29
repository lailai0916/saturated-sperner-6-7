import AiMathLab.P0054MiddleSevenNineExtension.Vector014
import AiMathLab.P0054MiddleSevenNineExtension.Selection014
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck012

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector014_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector014 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector014_selections]
  unfold sevenNineExtensionVector014Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector014_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
