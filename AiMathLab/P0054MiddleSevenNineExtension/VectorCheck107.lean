import AiMathLab.P0054MiddleSevenNineExtension.Vector107
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck105

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector107_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector107 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector107_selections]
  unfold sevenNineExtensionVector107Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector107_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
