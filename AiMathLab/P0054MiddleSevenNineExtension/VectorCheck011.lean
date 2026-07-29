import AiMathLab.P0054MiddleSevenNineExtension.Vector011
import AiMathLab.P0054MiddleSevenNineExtension.VectorCheck009

namespace AiMathLab.P0054.MiddleSevenNineExtensionFinite

open AiMathLab.P0054.G413
open AiMathLab.P0054.G420
open AiMathLab.P0054.MiddleSevenNineFinite

theorem sevenNineExtensionVector011_check :
    sevenNineExtensionValuesCheck sevenNineExtensionVector011 = true := by
  unfold sevenNineExtensionValuesCheck
  rw [sevenNineExtensionVector011_selections]
  unfold sevenNineExtensionVector011Selections
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sevenNineExtensionVector011_selection0_check]


end AiMathLab.P0054.MiddleSevenNineExtensionFinite
