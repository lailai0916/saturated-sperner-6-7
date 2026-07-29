import AiMathLab.P0054MiddleSevenNineExtension.Vector100
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck098

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector100_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector100 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector100_selections]
  unfold sevenNineExtensionVector100Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector100_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
