import AiMathLab.P0054MiddleSevenNineExtension.Vector052
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck050

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector052_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector052 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector052_selections]
  unfold sevenNineExtensionVector052Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector052_selection0_check]
  rw [sevenNineExtensionVector052_selection1_check]
  rw [sevenNineExtensionVector052_selection2_check]
  rw [sevenNineExtensionVector052_selection3_check]
  rw [sevenNineExtensionVector052_selection4_check]
  rw [sevenNineExtensionVector052_selection5_check]
  rw [sevenNineExtensionVector052_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
