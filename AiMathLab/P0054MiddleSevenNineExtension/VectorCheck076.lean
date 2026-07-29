import AiMathLab.P0054MiddleSevenNineExtension.Vector076
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck074

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector076_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector076 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector076_selections]
  unfold sevenNineExtensionVector076Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector076_selection0_check]
  rw [sevenNineExtensionVector076_selection1_check]
  rw [sevenNineExtensionVector076_selection2_check]
  rw [sevenNineExtensionVector076_selection3_check]
  rw [sevenNineExtensionVector076_selection4_check]
  rw [sevenNineExtensionVector076_selection5_check]
  rw [sevenNineExtensionVector076_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
