import AiMathLab.P0054MiddleSevenNineExtension.Vector004
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck002

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector004_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector004 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector004_selections]
  unfold sevenNineExtensionVector004Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector004_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
