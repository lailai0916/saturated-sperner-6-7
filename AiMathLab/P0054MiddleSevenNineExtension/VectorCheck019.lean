import AiMathLab.P0054MiddleSevenNineExtension.Vector019
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck017

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector019_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector019 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector019_selections]
  unfold sevenNineExtensionVector019Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector019_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
