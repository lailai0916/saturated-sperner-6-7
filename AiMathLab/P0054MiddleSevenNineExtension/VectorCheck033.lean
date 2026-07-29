import AiMathLab.P0054MiddleSevenNineExtension.Vector033
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck031

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector033_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector033 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector033_selections]
  unfold sevenNineExtensionVector033Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector033_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
