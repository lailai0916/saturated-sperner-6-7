import AiMathLab.P0054MiddleSevenNineExtension.Vector088
import AiMathLab.P0054MiddleSevenNineExtension.Selection088
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck086

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector088_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector088 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector088_selections]
  unfold sevenNineExtensionVector088Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector088_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
