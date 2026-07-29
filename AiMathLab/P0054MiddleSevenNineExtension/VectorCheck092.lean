import AiMathLab.P0054MiddleSevenNineExtension.Vector092
import AiMathLab.P0054MiddleSevenNineExtension.Selection092
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck090

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector092_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector092 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector092_selections]
  unfold sevenNineExtensionVector092Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector092_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
