import AiMathLab.P0054MiddleSevenNineExtension.Vector077
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck075

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector077_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector077 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector077_selections]
  unfold sevenNineExtensionVector077Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector077_selection0_check]
  rw [sevenNineExtensionVector077_selection1_check]
  rw [sevenNineExtensionVector077_selection2_check]
  rw [sevenNineExtensionVector077_selection3_check]
  rw [sevenNineExtensionVector077_selection4_check]
  rw [sevenNineExtensionVector077_selection5_check]
  rw [sevenNineExtensionVector077_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
