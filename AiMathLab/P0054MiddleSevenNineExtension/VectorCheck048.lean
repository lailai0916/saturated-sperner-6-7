import AiMathLab.P0054MiddleSevenNineExtension.Vector048
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck046

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector048_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector048 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector048_selections]
  unfold sevenNineExtensionVector048Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector048_selection0_check]
  rw [sevenNineExtensionVector048_selection1_check]
  rw [sevenNineExtensionVector048_selection2_check]
  rw [sevenNineExtensionVector048_selection3_check]
  rw [sevenNineExtensionVector048_selection4_check]
  rw [sevenNineExtensionVector048_selection5_check]
  rw [sevenNineExtensionVector048_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
