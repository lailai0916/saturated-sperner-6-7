import AiMathLab.P0054MiddleSevenNineExtension.Vector072
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck070

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector072_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector072 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector072_selections]
  unfold sevenNineExtensionVector072Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector072_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
