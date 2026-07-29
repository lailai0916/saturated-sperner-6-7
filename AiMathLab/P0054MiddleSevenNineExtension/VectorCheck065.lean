import AiMathLab.P0054MiddleSevenNineExtension.Vector065
import AiMathLab.P0054MiddleSevenNineExtension.Selection065
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck063

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector065_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector065 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector065_selections]
  unfold sevenNineExtensionVector065Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector065_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
