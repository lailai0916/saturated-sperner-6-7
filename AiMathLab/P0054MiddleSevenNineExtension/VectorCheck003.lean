import AiMathLab.P0054MiddleSevenNineExtension.Vector003
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck001

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector003_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector003 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector003_selections]
  unfold sevenNineExtensionVector003Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector003_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
