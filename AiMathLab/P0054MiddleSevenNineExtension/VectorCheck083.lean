import AiMathLab.P0054MiddleSevenNineExtension.Vector083
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck081

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector083_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector083 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector083_selections]
  unfold sevenNineExtensionVector083Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector083_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
