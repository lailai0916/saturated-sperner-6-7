import AiMathLab.P0054MiddleSevenNineExtension.Vector024
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck022

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector024_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector024 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector024_selections]
  unfold sevenNineExtensionVector024Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector024_selection0_check]
  rw [sevenNineExtensionVector024_selection1_check]
  rw [sevenNineExtensionVector024_selection2_check]
  rw [sevenNineExtensionVector024_selection3_check]
  rw [sevenNineExtensionVector024_selection4_check]
  rw [sevenNineExtensionVector024_selection5_check]
  rw [sevenNineExtensionVector024_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
