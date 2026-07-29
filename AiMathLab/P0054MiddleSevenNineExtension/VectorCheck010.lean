import AiMathLab.P0054MiddleSevenNineExtension.Vector010
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck008

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector010_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector010 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector010_selections]
  unfold sevenNineExtensionVector010Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector010_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
