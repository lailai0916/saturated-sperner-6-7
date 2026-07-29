import AiMathLab.P0054MiddleSevenNineExtension.Vector017
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck015

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector017_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector017 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector017_selections]
  unfold sevenNineExtensionVector017Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector017_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
