import AiMathLab.P0054MiddleSevenNineExtension.Vector066
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck064

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector066_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector066 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector066_selections]
  unfold sevenNineExtensionVector066Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector066_selection0_check]
  rw [sevenNineExtensionVector066_selection1_check]
  rw [sevenNineExtensionVector066_selection2_check]
  rw [sevenNineExtensionVector066_selection3_check]
  rw [sevenNineExtensionVector066_selection4_check]
  rw [sevenNineExtensionVector066_selection5_check]
  rw [sevenNineExtensionVector066_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
