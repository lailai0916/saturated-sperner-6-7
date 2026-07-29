import AiMathLab.P0054MiddleSevenNineExtension.Vector070
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck068

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector070_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector070 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector070_selections]
  unfold sevenNineExtensionVector070Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector070_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
