import AiMathLab.P0054MiddleSevenNineExtension.Vector018
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck016

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector018_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector018 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector018_selections]
  unfold sevenNineExtensionVector018Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector018_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
