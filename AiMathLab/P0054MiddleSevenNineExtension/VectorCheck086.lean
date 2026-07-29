import AiMathLab.P0054MiddleSevenNineExtension.Vector086
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck084

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector086_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector086 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector086_selections]
  unfold sevenNineExtensionVector086Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector086_selection0_check]
  rw [sevenNineExtensionVector086_selection1_check]
  rw [sevenNineExtensionVector086_selection2_check]
  rw [sevenNineExtensionVector086_selection3_check]
  rw [sevenNineExtensionVector086_selection4_check]
  decide

end AiMathLab.P0054.MiddleSevenNineExtensionFinite
