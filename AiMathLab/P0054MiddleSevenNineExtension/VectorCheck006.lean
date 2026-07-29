import AiMathLab.P0054MiddleSevenNineExtension.Vector006
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck004

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector006_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector006 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector006_selections]
  unfold sevenNineExtensionVector006Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector006_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
