import AiMathLab.P0054MiddleSevenNineExtension.Vector056
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck054

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector056_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector056 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector056_selections]
  unfold sevenNineExtensionVector056Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector056_selection0_check]
  rw [sevenNineExtensionVector056_selection1_check]
  rw [sevenNineExtensionVector056_selection2_check]
  rw [sevenNineExtensionVector056_selection3_check]
  rw [sevenNineExtensionVector056_selection4_check]
  rw [sevenNineExtensionVector056_selection5_check]
  rw [sevenNineExtensionVector056_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
