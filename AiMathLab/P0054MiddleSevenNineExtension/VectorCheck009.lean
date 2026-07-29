import AiMathLab.P0054MiddleSevenNineExtension.Vector009
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck007

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector009_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector009 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector009_selections]
  unfold sevenNineExtensionVector009Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector009_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
