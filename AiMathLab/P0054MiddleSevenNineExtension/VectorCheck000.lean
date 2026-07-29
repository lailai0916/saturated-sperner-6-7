import AiMathLab.P0054MiddleSevenNineExtension.Vector000

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector000_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector000 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector000_selections]
  unfold sevenNineExtensionVector000Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector000_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
