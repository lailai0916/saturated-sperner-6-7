import AiMathLab.P0054MiddleSevenNineExtension.Vector001

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector001_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector001 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector001_selections]
  unfold sevenNineExtensionVector001Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector001_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
