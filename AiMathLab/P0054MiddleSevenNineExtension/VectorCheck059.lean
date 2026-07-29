import AiMathLab.P0054MiddleSevenNineExtension.Vector059
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck057

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector059_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector059 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector059_selections]
  unfold sevenNineExtensionVector059Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector059_selection0_check]
  rw [sevenNineExtensionVector059_selection1_check]
  rw [sevenNineExtensionVector059_selection2_check]
  rw [sevenNineExtensionVector059_selection3_check]
  rw [sevenNineExtensionVector059_selection4_check]
  rw [sevenNineExtensionVector059_selection5_check]
  rw [sevenNineExtensionVector059_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
