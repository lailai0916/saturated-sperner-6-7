import AiMathLab.P0054MiddleSevenNineExtension.Vector068
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck066

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector068_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector068 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector068_selections]
  unfold sevenNineExtensionVector068Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector068_selection0_check]
  rw [sevenNineExtensionVector068_selection1_check]
  rw [sevenNineExtensionVector068_selection2_check]
  rw [sevenNineExtensionVector068_selection3_check]
  rw [sevenNineExtensionVector068_selection4_check]
  rw [sevenNineExtensionVector068_selection5_check]
  rw [sevenNineExtensionVector068_selection6_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
