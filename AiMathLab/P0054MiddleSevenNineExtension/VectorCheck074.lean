import AiMathLab.P0054MiddleSevenNineExtension.Vector074
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck072

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector074_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector074 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector074_selections]
  unfold sevenNineExtensionVector074Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector074_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
