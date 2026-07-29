import AiMathLab.P0054MiddleSevenNineExtension.Vector022
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck020

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector022_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector022 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector022_selections]
  unfold sevenNineExtensionVector022Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector022_selection0_check]
  rw [sevenNineExtensionVector022_selection1_check]
  rw [sevenNineExtensionVector022_selection2_check]
  rw [sevenNineExtensionVector022_selection3_check]
  rw [sevenNineExtensionVector022_selection4_check]
  rw [sevenNineExtensionVector022_selection5_check]
  rw [sevenNineExtensionVector022_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
