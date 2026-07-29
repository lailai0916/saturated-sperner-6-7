import AiMathLab.P0054MiddleSevenNineExtension.Vector049
import AiMathLab.P0054MiddleSevenNineExtension.Selection049
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck047

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector049_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector049 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector049_selections]
  unfold sevenNineExtensionVector049Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector049_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
