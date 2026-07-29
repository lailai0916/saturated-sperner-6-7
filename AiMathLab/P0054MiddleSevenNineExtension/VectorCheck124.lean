import AiMathLab.P0054MiddleSevenNineExtension.Vector124
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck122

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector124_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector124 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector124_selections]
  unfold sevenNineExtensionVector124Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector124_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
