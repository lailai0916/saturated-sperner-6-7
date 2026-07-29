import AiMathLab.P0054MiddleSevenNineExtension.Vector002
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck000

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector002_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector002 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector002_selections]
  unfold sevenNineExtensionVector002Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector002_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
