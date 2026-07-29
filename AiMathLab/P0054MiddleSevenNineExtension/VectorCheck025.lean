import AiMathLab.P0054MiddleSevenNineExtension.Vector025
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck023

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector025_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector025 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector025_selections]
  unfold sevenNineExtensionVector025Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector025_selection0_check]
  rw [sevenNineExtensionVector025_selection1_check]
  rw [sevenNineExtensionVector025_selection2_check]
  rw [sevenNineExtensionVector025_selection3_check]
  rw [sevenNineExtensionVector025_selection4_check]
  rw [sevenNineExtensionVector025_selection5_check]
  rw [sevenNineExtensionVector025_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
