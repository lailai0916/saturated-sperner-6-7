import AiMathLab.P0054MiddleSevenNineExtension.Vector085
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck083

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector085_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector085 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector085_selections]
  unfold sevenNineExtensionVector085Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector085_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
